-- | The parser for the SLD tree notation described in NOTATION.md.
--
-- The structure comes from indentation.  A node is a line starting with
-- @?-@.  The steps below it are lines starting with @|@, all in the same
-- column, which is to the right of the node.  A step may be followed by its
-- child, in the same column as the step: a node, or @\@name@, which stands
-- for the tree of that name written elsewhere in the file.
--
-- > ?- max(3, 5, M).
-- >   | max(X1, Y1, Y1) :- X1 =< Y1, !.
-- >   | {X1 |-> 3, Y1 |-> 5, M |-> 5}
-- >   ?- 3 =< 5, !.
-- >     | builtin
-- >     ?- !.                      @c
-- >       | !
-- >       ?- true.                 {M |-> 5}
-- >   | pruned max/3 #2            by @c
--
-- The parser only reads the notation.  Whether the tree is a correct SLD
-- tree is decided by "SLDCheck.Check".
module SLDCheck.Notation
  ( parseForest
  , parseForestWith
  ) where

import Control.Monad
import Text.Parsec

import SLDCheck.Prolog
import SLDCheck.Tree

parseForest :: SourceName -> String -> Either ParseError Forest
parseForest = parseForestWith defaultOps

-- | Use a custom operator table for the Prolog parts.  The bar is not an
--   infix operator here (write disjunction as @;@): a goal whose end dot was
--   forgotten would otherwise run into the @|@ of the next step.
parseForestWith :: OpTable -> SourceName -> String -> Either ParseError Forest
parseForestWith ops = runParser forest (addOp 0 XFY "|" ops)

--------------------------------------------------------------------------------
-- Helpers

position :: Parser Pos
position = (\p -> Pos (sourceLine p) (sourceColumn p)) <$> getPosition

column :: Parser Int
column = sourceColumn <$> getPosition

-- | A token followed by layout and comments.
tok :: Parser a -> Parser a
tok p = p <* ws

identChar :: Parser Char
identChar = alphaNum <|> char '_'

-- | A word that is not just the start of a longer name, and not the start of
--   a Prolog term such as @fails(x).@ or @fails.@.
word :: String -> Parser ()
word w = tok (try (string w *> notFollowedBy (identChar <|> char '.' <|> char '(')))

-- | Is the next character this one (without consuming it)?
peek :: Char -> Parser Bool
peek c = option False (True <$ lookAhead (char c))

peekString :: String -> Parser Bool
peekString s = option False (True <$ lookAhead (try (string s)))

--------------------------------------------------------------------------------
-- Forest and nodes

forest :: Parser Forest
forest = do
  ws
  c0 <- column
  first <- node
  rest  <- many (aligned c0)
  eof <?> "end of the file (another tree must start with \"?-\" in column " ++ show c0 ++ ")"
  pure (first : rest)
  where
    aligned c0 = do
      c <- column
      isNode <- peekString "?-"
      guard isNode <?> "a tree (\"?-\")"
      when (c /= c0) $
        fail ("a tree must start in column " ++ show c0 ++ ", like the first one")
      node

node :: Parser Node
node = do
  pos <- position
  n   <- column
  _   <- tok (try (string "?-")) <?> "a node (\"?-\")"
  g   <- term 1200 <?> "a goal"
  _   <- endDot <?> "the end dot of the goal (\".\")"
  name <- optionMaybe atName
  ans  <- optionMaybe subst
  steps <- stepsBelow n
  pure (Node pos name g ans steps)

-- | @\@name@
atName :: Parser String
atName = tok (char '@' *> many1 identChar) <?> "a node name (\"@name\")"

--------------------------------------------------------------------------------
-- Steps

-- | The steps of a node that sits in column @n@.
stepsBelow :: Int -> Parser [Step]
stepsBelow n = do
  c    <- column
  bar  <- peek '|'
  if bar && c > n then loop c else misaligned >> pure []
  where
    loop m = do
      c   <- column
      bar <- peek '|'
      if bar && c == m
        then (:) <$> step m <*> loop m
        else misaligned >> pure []

    -- something that belongs below the node, but at the wrong column
    misaligned = do
      c    <- column
      bar  <- peek '|'
      node' <- peekString "?-"
      ref   <- peek '@'
      when (c > n && (bar || node' || ref)) $
        fail (if bar then "this step is not aligned with the other steps of its node"
              else if ref then "this reference is not aligned with the step above it"
              else "this node is not aligned with the step above it")

step :: Int -> Parser Step
step m = do
  pos  <- position
  _    <- tok (char '|')
  kind <- stepHead
  hasSub <- option False (True <$ lookAhead (try (substStart m)))
  sub  <- if hasSub then substStart m *> (Just <$> subst) else pure Nothing
  c <- column
  isNode <- peekString "?-"
  isRef  <- peek '@'
  (child, ref) <-
    if c /= m then pure (Nothing, Nothing)
    else if isNode then (\nd -> (Just nd, Nothing)) <$> node
    else if isRef then do { p <- position; nm <- atName; pure (Nothing, Just (nm, p)) }
    else pure (Nothing, Nothing)
  pure (Step pos kind sub child ref)

-- | The start of the @| {...}@ line of a step: the bar, up to the brace.
substStart :: Int -> Parser ()
substStart m = do
  c <- column
  guard (c == m)
  _ <- tok (char '|')
  void (lookAhead (char '{'))

stepHead :: Parser StepKind
stepHead = choice
  [ pruned
  , Builtin <$ word "builtin" >>= \b -> option b (BuiltinFails <$ word "fails")
  , NoRule <$ (word "no" *> word "rule")
  , Fails <$ word "fails"
  , cut
  , negation
  , Resolve <$> rule
  ] <?> "a derivation step"
  where
    cut = try (CutStep <$ (tok (char '!') <* notFollowedBy (char '.')))

    negation = do
      _ <- try (tok (string "\\+") <* lookAhead (char '@'))
      t <- atName
      option (Negation t) (NegationFails t <$ word "fails")

    pruned = do
      word "pruned"
      pname <- tok (many1 identChar) <?> "a predicate name"
      _     <- tok (char '/')
      arity <- tok (read <$> many1 digit) <?> "an arity"
      _     <- tok (char '#') <?> "\"#\" and a clause number"
      k     <- tok (read <$> many1 digit) <?> "a clause number"
      word "by"
      c     <- atName
      pure (Pruned (pname, arity) k c)

rule :: Parser Term
rule = do
  r <- term 1200 <?> "a rule"
  _ <- endDot <?> "the end dot of the rule (\".\")"
  pure r

-- | @{ X |-> t, Y |-> u }@, possibly empty.
subst :: Parser Subst
subst = between (tok (char '{')) (tok (char '}')) (binding `sepBy` tok (char ','))

binding :: Parser (String, Term)
binding = do
  v <- variable <* ws
  name <- case v of
    Var x -> pure x
    _     -> fail "a variable"
  _ <- tok (try (string "|->")) <?> "\"|->\""
  t <- term 999
  pure (name, t)
