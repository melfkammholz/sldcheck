{-# LANGUAGE TupleSections #-}

-- | Prolog terms: syntax, operator tables, parsing and printing.
module SLDCheck.Prolog
  ( Term(..)
  , OpType(..)
  , OpTable
  , defaultOps
  , addOp
  , Parser
  , term
  , ws
  , variable
  , endDot
  , parseTerm
  , parseTermWith
  , parseProgram
  , parseProgramOps
  , showTermWith
  , atomText
  , symbolChars
  ) where

import Control.Monad
import Data.Char
import Data.List (intercalate, isPrefixOf)
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes, fromMaybe)
import Numeric (showHex)
import Text.Parsec

--------------------------------------------------------------------------------
-- AST

data Term
  = Atom String
  | Var String
  | IntLit Integer
  | FloatLit Double
  | StrLit String
  | Compound String [Term]
  | List [Term] (Maybe Term)        -- ^ @[a,b|T]@; @[]@ is @Atom "[]"@
  deriving Eq
  -- 'Show' is a hand-written instance that prints Prolog syntax (see the end
  -- of this file).

--------------------------------------------------------------------------------
-- Operator table

data OpType = XFX | XFY | YFX | FY | FX
  deriving (Eq, Show, Read)

data OpTable = OpTable
  { prefixOps :: M.Map String (Int, OpType)
  , infixOps  :: M.Map String (Int, OpType)
  }

-- | Add (or, with priority 0, remove) an operator.
addOp :: Int -> OpType -> String -> OpTable -> OpTable
addOp p ty name t
  | ty `elem` [FY, FX] = t { prefixOps = upd (prefixOps t) }
  | otherwise          = t { infixOps  = upd (infixOps t) }
  where
    upd | p == 0    = M.delete name
        | otherwise = M.insert name (p, ty)

-- | Roughly the SWI-Prolog / ISO default table.
defaultOps :: OpTable
defaultOps = foldl' (\t (p, ty, ns) -> foldl' (flip (addOp p ty)) t ns)
                    (OpTable M.empty M.empty)
  [ (1200, XFX, [":-", "-->"])
  , (1200, FX,  [":-", "?-"])
  , (1150, FX,  ["dynamic", "discontiguous", "initialization", "table"])
  , (1100, XFY, [";", "|"])
  , (1050, XFY, ["->", "*->"])
  , (1000, XFY, [","])
  , (900,  FY,  ["\\+"])
  , (700,  XFX, [ "=", "\\=", "==", "\\==", "@<", "@>", "@=<", "@>=", "=..", "is"
                , "=:=", "=\\=", "<", ">", "=<", ">=", ">:<", ":<", "as" ])
  , (600,  XFY, [":"])
  , (500,  YFX, ["+", "-", "/\\", "\\/", "xor"])
  , (400,  YFX, ["*", "/", "//", "mod", "rem", "<<", ">>", "div", "rdiv"])
  , (200,  XFX, ["**"])
  , (200,  XFY, ["^"])
  , (200,  FY,  ["-", "+", "\\"])
  ]

leftMax, rightMax :: Int -> OpType -> Int
leftMax  p ty = if ty == YFX then p else p - 1
rightMax p ty = if ty == XFY then p else p - 1

--------------------------------------------------------------------------------
-- Lexical layer

type Parser = Parsec String OpTable

-- | Skip whitespace and comments.
ws :: Parser ()
ws = skipMany (void (satisfy isSpace) <|> lineComment <|> blockComment)
  where
    lineComment  = char '%' *> skipMany (noneOf "\n")
    blockComment = void (try (string "/*") *> manyTill anyChar (try (string "*/")))

lexeme :: Parser a -> Parser a
lexeme p = p <* ws

sym :: Char -> Parser Char
sym = lexeme . char

identChar :: Parser Char
identChar = alphaNum <|> char '_'

symbolChars :: String
symbolChars = "+-*/\\^<>=~:.?@#&$"

-- | A run of symbol characters.  A lone "." is the end token, not an atom.
symbolAtom :: Parser String
symbolAtom = try $ do
  s <- many1 (oneOf symbolChars)
  when (s == ".") $ unexpected "end of clause"
  pure s

alnumAtom :: Parser String
alnumAtom = (:) <$> lower <*> many identChar

-- | An atom token without trailing whitespace; the Bool says "was quoted".
atomRaw :: Parser (String, Bool)
atomRaw = choice
  [ (, False) <$> alnumAtom
  , (, True)  <$> quotedWith '\''
  , (, False) <$> symbolAtom
  , (, False) <$> (string "!" <|> string ";")
  ] <?> "atom"

variable :: Parser Term
variable = Var <$> ((:) <$> (upper <|> char '_') <*> many identChar) <?> "variable"

-- Quoted items ---------------------------------------------------------------

quotedWith :: Char -> Parser String
quotedWith q = between (char q) (char q <?> "closing quote")
                       (catMaybes <$> many item)
  where
    item =  Just q <$ try (string [q, q])            -- doubled quote
        <|> escape
        <|> Just <$> noneOf [q, '\\']

-- | Nothing means a line continuation (backslash-newline).
escape :: Parser (Maybe Char)
escape = char '\\' *> choice
  [ Nothing <$ char '\n'
  , Just . chr . fromInteger . readBase 16 <$> (char 'x' *> many1 hexDigit <* char '\\')
  , Just . chr . fromInteger . readBase 8  <$> (many1 octDigit <* char '\\')
  , Just <$> simple
  ] <?> "escape sequence"
  where
    simple = do
      c <- anyChar
      maybe (fail ("unknown escape \\" ++ [c])) pure (lookup c table)
    table = [ ('n','\n'), ('t','\t'), ('r','\r'), ('a','\a'), ('b','\b')
            , ('f','\f'), ('v','\v'), ('e','\ESC'), ('s',' '), ('\\','\\')
            , ('\'','\''), ('"','"'), ('`','`') ]

readBase :: Integer -> String -> Integer
readBase b = foldl' (\a d -> a * b + toInteger (digitToInt d)) 0

-- Numbers --------------------------------------------------------------------

number :: Parser Term
number = choice
  [ try (string "0'") *> (IntLit . toInteger <$> charCode)
  , try (string "0x") *> (IntLit . readBase 16 <$> many1 hexDigit)
  , try (string "0o") *> (IntLit . readBase 8  <$> many1 octDigit)
  , try (string "0b") *> (IntLit . readBase 2  <$> many1 (oneOf "01"))
  , decimal
  ] <?> "number"
  where
    charCode =  ord '\'' <$ try (string "''")
            <|> (escape >>= maybe (fail "bad character code") (pure . ord))
            <|> ord <$> anyChar

    decimal = do
      ds   <- many1 digit
      frac <- optionMaybe (try (char '.' *> many1 digit))
      ex   <- optionMaybe (try expo)
      pure $ case (frac, ex) of
        (Nothing, Nothing) -> IntLit (read ds)
        _ -> FloatLit (read (ds ++ "." ++ fromMaybe "0" frac
                                ++ "e" ++ fromMaybe "0" ex))

    expo = oneOf "eE" *>
           ((++) <$> option "" ("-" <$ char '-' <|> "" <$ char '+') <*> many1 digit)

negateNum :: Term -> Term
negateNum (IntLit n)   = IntLit (negate n)
negateNum (FloatLit x) = FloatLit (negate x)
negateNum t            = t

--------------------------------------------------------------------------------
-- Terms

-- | Parse a term whose priority is at most the given bound.
--   Use 1200 for a full term and 999 for an argument.
term :: Int -> Parser Term
term maxP = primary maxP >>= uncurry (infixLoop maxP)

-- | A primary term together with its priority.
primary :: Int -> Parser (Term, Int)
primary maxP = choice
  [ p0 <$> lexeme number
  , p0 <$> lexeme variable
  , p0 . StrLit <$> lexeme (quotedWith '"')
  , p0 <$> list
  , p0 <$> curly
  , p0 <$> parens
  , atomLike maxP
  ]
  where p0 = (, 0)

parens :: Parser Term
parens = sym '(' *> term 1200 <* sym ')'

curly :: Parser Term
curly = sym '{' *>
  (Atom "{}" <$ sym '}' <|> Compound "{}" . pure <$> term 1200 <* sym '}')

list :: Parser Term
list = sym '[' *>
  (Atom "[]" <$ sym ']' <|> do
      items <- term 999 `sepBy1` sym ','
      tl    <- optionMaybe (sym '|' *> term 999)
      _     <- sym ']'
      pure (List items tl))

-- | Atoms, compound terms f(...), negative literals and prefix operators.
atomLike :: Int -> Parser (Term, Int)
atomLike maxP = do
  (name, quoted) <- atomRaw
  -- functional notation requires '(' immediately after the name
  margs <- optionMaybe (char '(' *> ws *> (term 999 `sepBy1` sym ',') <* sym ')')
  case margs of
    Just args -> ws >> pure (Compound name args, 0)
    Nothing
      | name == "-" && not quoted -> do
          isNum <- optionMaybe (lookAhead digit)
          case isNum of
            Just _  -> (, 0) . negateNum <$> lexeme number
            Nothing -> ws >> prefixOrAtom name
      | otherwise -> ws >> prefixOrAtom name
  where
    prefixOrAtom name = do
      ops <- getState
      case M.lookup name (prefixOps ops) of
        Nothing -> pure (Atom name, 0)
        Just (p, ty) -> do
          infixOnly <- nextIsInfixOnly
          if infixOnly
            then pure (Atom name, 0)            -- e.g.  f(-, a)   or   - = X
            else
              let argMax = min maxP (if ty == FY then p else p - 1)
                  resP   = min p maxP
              in  try (do a <- term argMax
                          pure (Compound name [a], resP))
                  <|> pure (Atom name, 0)       -- e.g.  [-]   or   foo(dynamic)

-- | Is the next token an infix operator that cannot also start a term?
nextIsInfixOnly :: Parser Bool
nextIsInfixOnly = do
  ops <- getState
  option False . lookAhead . try $ do
    n <- choice [string ",", string "|", fst <$> atomRaw]
    notFollowedBy (char '(')          -- `*(a)` is a term, not an operator
    pure (M.member n (infixOps ops) && not (M.member n (prefixOps ops)))

-- | A token that might be an infix operator.
infixName :: Parser String
infixName = lexeme $ choice [string ",", string "|", fst <$> atomRaw]

-- | Precedence climbing for infix operators.
infixLoop :: Int -> Term -> Int -> Parser Term
infixLoop maxP left leftP = step <|> pure left
  where
    step = do
      (name, p, ty) <- try $ do
        n   <- infixName
        ops <- getState
        (p, ty) <- maybe (fail "not an infix operator") pure
                         (M.lookup n (infixOps ops))
        guard (p <= maxP && leftP <= leftMax p ty)
        pure (n, p, ty)
      right <- term (rightMax p ty)
      let functor = if name == "|" then ";" else name
      infixLoop maxP (Compound functor [left, right]) p

--------------------------------------------------------------------------------
-- Clauses and programs

-- | The end-of-clause token: a '.' followed by layout, a comment or EOF.
endDot :: Parser ()
endDot = lexeme . try $
  char '.' *> lookAhead (void (satisfy isSpace) <|> void (char '%') <|> eof)

clause :: Parser Term
clause = do
  t <- term 1200
  endDot <?> "end of clause (\".\")"
  applyDirective t
  pure t

-- | Handle @:- op(P, Type, Names).@ by updating the operator table.
applyDirective :: Term -> Parser ()
applyDirective (Compound ":-" [Compound "op" [IntLit p, Atom ty, names]])
  | [(t, "")] <- reads (map toUpper ty) =
      mapM_ (modifyState . addOp (fromInteger p) t) (opNames names)
  where
    opNames (Atom n)             = [n]
    opNames (List as Nothing)    = [n | Atom n <- as]
    opNames _                    = []
applyDirective _ = pure ()

-- | Parse a single term (an optional trailing '.' is allowed).
parseTerm :: String -> Either ParseError Term
parseTerm = parseTermWith defaultOps

parseTermWith :: OpTable -> String -> Either ParseError Term
parseTermWith ops = runParser (ws *> term 1200 <* optional endDot <* eof) ops "<term>"

-- | Parse a whole file of clauses.  @op/3@ directives take effect for the
--   clauses that follow them.
parseProgram :: SourceName -> String -> Either ParseError [Term]
parseProgram name src = fst <$> parseProgramOps name src

-- | Like 'parseProgram', and also returns the operator table as it is after
--   the last @op/3@ directive, so that other text can be read with it.
parseProgramOps :: SourceName -> String -> Either ParseError ([Term], OpTable)
parseProgramOps = runParser ((,) <$> (ws *> many clause <* eof) <*> getState) defaultOps

--------------------------------------------------------------------------------
-- Printing

-- | Terms are shown as Prolog source, using 'defaultOps' for operators:
--
--   * infix operators are surrounded by spaces (@X is Y + 1@, @a :- b@) except
--     the comma, which is written @a, b@; arguments and list elements are
--     separated by @", "@
--   * parentheses are added only where priorities require them
--   * atoms are quoted when necessary (@'Hello world'@, @'it\'s'@)
--   * operator atoms used as operands are bracketed, e.g. @(-) = X@
--
--   The output can be read back with 'parseTerm' and gives the same term.
--   When a term is shown as an argument of a Haskell constructor, operator
--   terms and negative numbers get an extra pair of parentheses.
instance Show Term where
  showsPrec d t = showParen paren (showString (showTermWith defaultOps t))
    where
      paren = (d > 10 && isOpTerm defaultOps t) || (d > 6 && isNegative t)
      isNegative (IntLit n)   = n < 0
      isNegative (FloatLit x) = x < 0
      isNegative _            = False

isOpTerm :: OpTable -> Term -> Bool
isOpTerm ops (Compound f [_, _]) = M.member f (infixOps ops)
isOpTerm ops (Compound f [_])    = M.member f (prefixOps ops)
isOpTerm _   _                   = False

-- | Render a term with a custom operator table.
showTermWith :: OpTable -> Term -> String
showTermWith ops = render ops False 1200

-- | @render ops operand maxP t@ prints @t@ where a term of priority at most
--   @maxP@ is allowed.  @operand@ says whether @t@ is an operand of an
--   operator (as opposed to a top-level term, an argument or a list element);
--   it only matters for operator atoms.
render :: OpTable -> Bool -> Int -> Term -> String
render ops operand maxP t = case t of
  Var v        -> v
  IntLit n     -> show n
  FloatLit x   -> show x
  StrLit s     -> quoteWith '"' s
  Atom a       -> atom a
  List [] Nothing    -> "[]"
  List [] (Just tl)  -> arg tl
  List xs tl   -> "[" ++ intercalate ", " (map arg xs)
                      ++ maybe "" (\x -> "|" ++ arg x) tl ++ "]"
  Compound "{}" [x] -> "{" ++ render ops False 1200 x ++ "}"

  Compound f [l, r]
    | Just (p, ty) <- M.lookup f (infixOps ops) ->
        par (p > maxP) $
          render ops True (leftMax p ty) l ++ infixText f
            ++ render ops True (rightMax p ty) r

  Compound f [x]
    | Just (p, ty) <- M.lookup f (prefixOps ops) ->
        let s = render ops True (if ty == FY then p else p - 1) x
        in if f `elem` ["-", "+"] && startsWith isDigit s
             -- "-1" would be read as a number, so use f(...) notation
             then f ++ "(" ++ arg x ++ ")"
             else par (p > maxP) (f ++ prefixSpace f p s ++ s)

  Compound f args -> atomText f ++ "(" ++ intercalate ", " (map arg args) ++ ")"
  where
    arg = render ops False 999

    par b s = if b then "(" ++ s ++ ")" else s

    atom a
      | needsParens = "(" ++ atomText a ++ ")"
      | otherwise   = atomText a
      where
        needsParens = case opPriority a of
          Nothing -> False
          Just p  -> operand || p > maxP

    opPriority a = case [p | Just (p, _) <- [M.lookup a (prefixOps ops), M.lookup a (infixOps ops)]] of
      [] -> Nothing
      ps -> Just (maximum ps)

    infixText "," = ", "
    infixText "|" = " | "
    infixText f   = " " ++ f ++ " "

    -- A space after a prefix operator is needed to keep tokens apart, and is
    -- always written for "statement-like" operators (\+, :-, dynamic, ...).
    prefixSpace f p s
      | p > 200 || startsWith isAlpha f                = " "
      | startsWith (\c -> c `elem` symbolChars || c == '(') s = " "
      | otherwise                                      = ""

    startsWith q (c:_) = q c
    startsWith _ []    = False

-- | An atom, quoted if it would not be read back as the same atom.
atomText :: String -> String
atomText a
  | plain     = a
  | otherwise = quoteWith '\'' a
  where
    plain = a `elem` ["[]", "{}", "!", ";"] || alnum || symbolic
    alnum = case a of
      c:cs -> isLower c && all (\x -> isAlphaNum x || x == '_') cs
      []   -> False
    symbolic = not (null a) && all (`elem` symbolChars) a
               && a /= "." && not ("/*" `isPrefixOf` a)

quoteWith :: Char -> String -> String
quoteWith q s = [q] ++ concatMap esc s ++ [q]
  where
    esc c
      | c == q       = ['\\', q]
      | c == '\\'    = "\\\\"
      | c == '\n'    = "\\n"
      | c == '\t'    = "\\t"
      | c == '\r'    = "\\r"
      | isControl c  = "\\x" ++ showHex (ord c) "" ++ "\\"
      | otherwise    = [c]
