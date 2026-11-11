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
import Data.Char (isSpace)
import Data.List (dropWhileEnd)
import Data.Maybe (listToMaybe)
import Text.Parsec
import Text.Parsec.Error (Message(..), errorMessages, newErrorMessage)
import Text.Parsec.Pos (newPos, updatePosString)

import SLDCheck.Prolog
import SLDCheck.Tree

parseForest :: SourceName -> String -> Either ParseError Forest
parseForest = parseForestWith defaultOps

-- | Use a custom operator table for the Prolog parts.  The bar is not an
--   infix operator here (write disjunction as @;@): a goal whose end dot was
--   forgotten would otherwise run into the @|@ of the next step.
parseForestWith :: OpTable -> SourceName -> String -> Either ParseError Forest
parseForestWith ops name src = case leadingTab src of
  Just (l, c) -> Left (newErrorMessage (Message "tabs are not allowed in the indentation: use spaces") (newPos name l c))
  Nothing     -> either (Left . relocate name) Right (runParser forest (addOp 0 XFY "|" ops) name src)

-- | The first tab among the spaces that indent a line.  Editors count a tab as
--   one column and Parsec as up to eight, so the positions of everything after
--   it would be wrong; the structure of a tree is its indentation anyway.
leadingTab :: String -> Maybe (Int, Int)
leadingTab src = listToMaybe [ (l, length (takeWhile (== ' ') ln) + 1)
                             | (l, ln) <- zip [1 ..] (lines src), '\t' `elem` takeWhile isSpace ln ]

-- | Parsec reports an error where reading stopped.  For a brace that is never
--   closed or an end dot that is missing that is somewhere else than the problem,
--   so such a failure carries the place it is about (see 'failAt'), which is
--   put back into the error here.
relocate :: SourceName -> ParseError -> ParseError
relocate name err = case [m | Message m <- errorMessages err, take 1 m == "\0"] of
  m : _ -> let (loc, rest) = break (== '\0') (drop 1 m)
               (l, c)      = break (== ':') loc
           in newErrorMessage (Message (drop 1 rest)) (newPos name (read l) (read (drop 1 c)))
  []    -> err

-- | Fail with a message about an earlier place.  Parsec merges an error that
--   consumed nothing with what the parsers before it expected, and keeps the one
--   that is further on, so a character is consumed first: then the error stands
--   alone.  It is moved to the right place by 'relocate'.
failAt :: SourcePos -> String -> Parser a
failAt p msg = optional anyChar >> fail ("\0" ++ show (sourceLine p) ++ ":" ++ show (sourceColumn p) ++ "\0" ++ msg)

-- | A term, and the place right after its last token (the layout after it does not count).
termEnding :: Int -> Parser (Term, SourcePos)
termEnding prio = do
  start  <- getPosition
  before <- getInput
  t      <- term prio
  after  <- getInput
  let consumed = take (length before - length after) before
  pure (t, updatePosString start (dropWhileEnd isSpace consumed))

-- | The end dot of what was just read, which ended at the given place.
endDotAfter :: String -> SourcePos -> Parser ()
endDotAfter what p = do
  found <- optionMaybe endDot
  case found of
    Just () -> pure ()
    Nothing -> failAt p ("the end dot (\".\") of " ++ what ++ " is missing")

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
  (g, gEnd) <- termEnding 1200 <?> "a goal"
  endDotAfter "the goal" gEnd
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
  pure (Step pos kind sub child ref Nothing)

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
  (r, rEnd) <- termEnding 1200 <?> "a rule"
  endDotAfter "the rule" rEnd
  pure r

-- | @{ X |-> t, Y |-> u }@, possibly empty.
subst :: Parser Subst
subst = do
  open <- getPosition
  _    <- tok (char '{')
  bs   <- binding `sepBy` tok (char ',')
  closed <- optionMaybe (tok (char '}'))
  case closed of
    Just _  -> pure bs
    Nothing -> failAt open "this brace is never closed: expected \",\" or \"}\" after the last binding"

binding :: Parser (String, Term)
binding = do
  v <- variable <* ws
  name <- case v of
    Var x -> pure x
    _     -> fail "a variable"
  _ <- tok (try (string "|->")) <?> "\"|->\""
  t <- term 999
  pure (name, t)
