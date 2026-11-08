-- | What the checker reports.  Every diagnostic has a stable code (so that
--   tools and tests can rely on it), a severity, a place in the source and a
--   message that says what is wrong and, where possible, what would be right.
module SLDCheck.Diagnostic
  ( Severity(..)
  , Role(..)
  , Diagnostic(..)
  , Files(..)
  , diagnostic
  , sortDiagnostics
  , hasErrors
  , isSyntaxError
  , renderText
  , renderJson
  ) where

import Data.Char (ord)
import Data.List (intercalate, sortOn)
import Data.Maybe (fromMaybe)
import Numeric (showHex)

import SLDCheck.Tree (Pos(..))
import SLDCheck.Version (version)

data Severity = Info | Warning | Error
  deriving (Eq, Ord, Show, Enum)

-- | Which of the two inputs a diagnostic is about.
data Role = InTree | InProgram
  deriving (Eq, Ord, Show)

data Diagnostic = Diagnostic
  { dSeverity :: Severity
  , dCode     :: String      -- ^ for example @E022@
  , dRole     :: Role
  , dPos      :: Pos         -- ^ where the problem starts
  , dEnd      :: Maybe Pos   -- ^ where it ends (exclusive), if known; the command line fills in the end of the line
  , dMessage  :: String
  } deriving (Eq, Show)

-- | A diagnostic about the tree, with no end position yet.
diagnostic :: Severity -> String -> Pos -> String -> Diagnostic
diagnostic sev code pos = Diagnostic sev code InTree pos Nothing

-- | By position, then severity (errors first), keeping the order of the
--   checks otherwise.
sortDiagnostics :: [Diagnostic] -> [Diagnostic]
sortDiagnostics = sortOn (\d -> (dRole d, dPos d, negate (fromEnum (dSeverity d))))

hasErrors :: [Diagnostic] -> Bool
hasErrors = any ((== Error) . dSeverity)

-- | The input could not be read at all (codes @S001@ and @S002@).
isSyntaxError :: Diagnostic -> Bool
isSyntaxError d = take 1 (dCode d) == "S"

severityWord :: Severity -> String
severityWord Info    = "info"
severityWord Warning = "warning"
severityWord Error   = "error"

-- | The names of the files, as the user gave them.
data Files = Files { treeFile :: FilePath, programFile :: Maybe FilePath }

fileOf :: Files -> Role -> FilePath
fileOf fs InTree    = treeFile fs
fileOf fs InProgram = fromMaybe "program" (programFile fs)

-- | @file:line:col: error[E022]: message@, one per diagnostic, and a summary.
renderText :: Files -> [Diagnostic] -> String
renderText fs ds = unlines (map one ds ++ [summary])
  where
    one d = fileOf fs (dRole d) ++ ":" ++ show (posLine (dPos d)) ++ ":" ++ show (posCol (dPos d))
         ++ ": " ++ severityWord (dSeverity d) ++ "[" ++ dCode d ++ "]: "
         ++ indentRest (dMessage d)
    indentRest = intercalate "\n    " . lines
    count s = length [() | d <- ds, dSeverity d == s]
    file = treeFile fs
    summary
      | null ds   = file ++ ": no problems found"
      | otherwise = file ++ ": " ++ plural (count Error) "error" ++ ", "
                         ++ plural (count Warning) "warning" ++ ", "
                         ++ plural (count Info) "note"
    plural n w = show n ++ " " ++ w ++ (if n == 1 then "" else "s")

-- | A JSON object: the version of sldcheck and the @diagnostics@, each with
--   @severity@, @code@, @file@ (as the user gave it), @line@, @column@,
--   @endLine@, @endColumn@ (exclusive) and @message@.  Lines and columns start at 1.
renderJson :: Files -> [Diagnostic] -> String
renderJson fs ds = "{\"version\":" ++ str version ++ ",\"diagnostics\":["
  ++ intercalate ",\n  " (map one ds) ++ "]}\n"
  where
    one d = let Pos l c   = dPos d
                Pos l' c' = fromMaybe (Pos l (c + 1)) (dEnd d)
            in "{\"severity\":" ++ str (severityWord (dSeverity d))
               ++ ",\"code\":" ++ str (dCode d)
               ++ ",\"file\":" ++ str (fileOf fs (dRole d))
               ++ ",\"line\":" ++ show l ++ ",\"column\":" ++ show c
               ++ ",\"endLine\":" ++ show l' ++ ",\"endColumn\":" ++ show c'
               ++ ",\"message\":" ++ str (dMessage d) ++ "}"
    str s = "\"" ++ concatMap esc s ++ "\""
    esc c = case c of
      '"'  -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\t' -> "\\t"
      _ | ord c < 0x20 -> "\\u" ++ replicate (4 - length h) '0' ++ h
        | otherwise    -> [c]
      where h = showHex (ord c) ""
