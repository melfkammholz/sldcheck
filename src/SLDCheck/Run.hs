-- | What the command line does, without the file system: read the program and
--   the tree, and report what is wrong with them.  The syntax errors of both
--   come out as diagnostics too (@S001@ in the tree, @S002@ in the program),
--   with the other kinds, so that a caller only has to read one format.
module SLDCheck.Run
  ( Input(..)
  , Job(..)
  , analyse
  , readTree
  , fromParseError
  ) where

import Data.Char (isAlphaNum, isSpace)
import Data.List (dropWhileEnd)
import Data.Maybe (isJust)
import Text.Parsec (ParseError, errorPos, sourceColumn, sourceLine)
import Text.Parsec.Error (errorMessages, showErrorMessages)

import SLDCheck.Check
import SLDCheck.Diagnostic
import SLDCheck.Expand
import SLDCheck.Notation
import SLDCheck.Prolog
import SLDCheck.Tree (Forest, Pos(..))

-- | A file as it was read, with the name the user gave it.
data Input = Input { inputName :: FilePath, inputText :: String }

data Job
  = CheckTree { jobRequireAnswers :: Bool, jobAllowAnonymous :: Bool, jobProgram :: Input, jobTree :: Input }
    -- ^ everything: the tree is checked against the program
  | SyntaxOnly { jobProgramMaybe :: Maybe Input, jobTree :: Input }
    -- ^ only read the tree (and the program, if there is one, for its operators)

analyse :: Job -> [Diagnostic]
analyse job = completeEnds (inputText tree) (maybe "" inputText mprog) result
  where
    tree  = jobTree job
    mprog = case job of
      CheckTree { jobProgram = p }      -> Just p
      SyntaxOnly { jobProgramMaybe = p } -> p

    result = case readProgram of
      Left d   -> [d]
      Right mp -> case parseForestWith (maybe defaultOps snd mp) (inputName tree) (inputText tree) of
        Left e       -> [fromParseError InTree (inputText tree) e]
        Right forest -> case job of
          SyntaxOnly {}                   -> []
          CheckTree { jobRequireAnswers = req, jobAllowAnonymous = anon } ->
            checkForest ((defaultOptions (maybe [] fst mp)) { optRequireAnswers = req, optAllowAnonymous = anon }) forest

    readProgram = case mprog of
      Nothing -> Right Nothing
      Just p  -> case parseProgramOps (inputName p) (inputText p) of
        Left e  -> Left (fromParseError InProgram (inputText p) e)
        Right r -> Right (Just r)

-- | Read the tree (and the program, for its operators), and replace the
--   references between trees.  Syntax errors come back as diagnostics, with
--   the problems the references have, but without a forest.
readTree :: Maybe Input -> Input -> ([Diagnostic], Maybe (OpTable, Forest))
readTree mprog tree = completeAll $ case parseProgram' of
  Left d   -> ([d], Nothing)
  Right mp ->
    let ops = maybe defaultOps snd mp
    in case parseForestWith ops (inputName tree) (inputText tree) of
         Left e       -> ([fromParseError InTree (inputText tree) e], Nothing)
         Right forest -> let (expanded, ds) = expandForest forest in (ds, Just (ops, numberRules (maybe [] fst mp) expanded))
  where
    parseProgram' = case mprog of
      Nothing -> Right Nothing
      Just p  -> case parseProgramOps (inputName p) (inputText p) of
        Left e  -> Left (fromParseError InProgram (inputText p) e)
        Right r -> Right (Just r)
    completeAll (ds, r) = (completeEnds (inputText tree) (maybe "" inputText mprog) ds, r)

-- | A syntax error as a diagnostic: where reading stopped (or the place the
--   parser says is meant), up to the end of the token there, and what was
--   expected.
fromParseError :: Role -> String -> ParseError -> Diagnostic
fromParseError role src err =
  (diagnostic Error (if role == InTree then "S001" else "S002") pos message)
    { dRole = role, dEnd = Just (tokenEnd src pos) }
  where
    p   = errorPos err
    pos = Pos (sourceLine p) (sourceColumn p)
    raw = dropWhile (== '\n') (showErrorMessages "or" "unknown parse error" "expecting" "unexpected" "end of input" (errorMessages err))
    message = case lines raw of
      []           -> "Syntax error"
      first : rest -> unlines' (("Syntax error: " ++ first) : rest)
    unlines' = foldr1 (\a b -> a ++ "\n" ++ b)

-- | Give every diagnostic without an end the end of its line.
completeEnds :: String -> String -> [Diagnostic] -> [Diagnostic]
completeEnds tree prog = map fill
  where
    fill d | isJust (dEnd d) = d
           | otherwise       = d { dEnd = Just (lineEnd (source d) (dPos d)) }
    source d = if dRole d == InTree then tree else prog

-- | The end of the code on a line: not the layout after it, and not a comment.
lineEnd :: String -> Pos -> Pos
lineEnd src (Pos l c) = Pos l (max (c + 1) (length (dropWhileEnd isSpace (withoutComment (lineAt src l))) + 1))

-- | A line up to its @%@ comment, if it has one (a @%@ in quotes is not one).
withoutComment :: String -> String
withoutComment = go Nothing
  where
    go _ []                         = []
    go Nothing ('%' : _)            = []
    go Nothing (ch : rest)
      | ch `elem` "'\"`"            = ch : go (Just ch) rest
    go (Just q) (ch : rest)
      | ch == q                     = ch : go Nothing rest
    go q (ch : rest)                = ch : go q rest

-- | The word or the single character that starts at a place.
tokenEnd :: String -> Pos -> Pos
tokenEnd src (Pos l c) = case drop (c - 1) (lineAt src l) of
  x : xs | isWordChar x -> Pos l (c + 1 + length (takeWhile isWordChar xs))
  _                     -> Pos l (c + 1)
  where isWordChar ch = isAlphaNum ch || ch == '_'

lineAt :: String -> Int -> String
lineAt src l = case drop (l - 1) (lines src) of
  ln : _ -> ln
  []     -> ""
