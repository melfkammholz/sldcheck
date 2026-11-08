-- | What the checker reports.  Every diagnostic has a stable code (so that
--   tools and tests can rely on it), a severity, a place in the source and a
--   message that says what is wrong and, where possible, what would be right.
module SLDCheck.Diagnostic
  ( Severity(..)
  , Diagnostic(..)
  , sortDiagnostics
  , hasErrors
  , renderText
  , renderJson
  ) where

import Data.Char (ord)
import Data.List (intercalate, sortOn)
import Numeric (showHex)

import SLDCheck.Tree (Pos(..))

data Severity = Info | Warning | Error
  deriving (Eq, Ord, Show, Enum)

data Diagnostic = Diagnostic
  { dSeverity :: Severity
  , dCode     :: String      -- ^ for example @E022@
  , dPos      :: Pos
  , dMessage  :: String
  } deriving (Eq, Show)

-- | By position, then severity (errors first), keeping the order of the
--   checks otherwise.
sortDiagnostics :: [Diagnostic] -> [Diagnostic]
sortDiagnostics = sortOn (\d -> (dPos d, negate (fromEnum (dSeverity d))))

hasErrors :: [Diagnostic] -> Bool
hasErrors = any ((== Error) . dSeverity)

severityWord :: Severity -> String
severityWord Info    = "info"
severityWord Warning = "warning"
severityWord Error   = "error"

-- | @file:line:col: error[E022]: message@, one per diagnostic, and a summary.
renderText :: FilePath -> [Diagnostic] -> String
renderText file ds = unlines (map one ds ++ [summary])
  where
    one d = file ++ ":" ++ show (posLine (dPos d)) ++ ":" ++ show (posCol (dPos d))
         ++ ": " ++ severityWord (dSeverity d) ++ "[" ++ dCode d ++ "]: "
         ++ indentRest (dMessage d)
    indentRest = intercalate "\n    " . lines
    count s = length [() | d <- ds, dSeverity d == s]
    summary
      | null ds   = file ++ ": no problems found"
      | otherwise = file ++ ": " ++ plural (count Error) "error" ++ ", "
                         ++ plural (count Warning) "warning" ++ ", "
                         ++ plural (count Info) "note"
    plural n w = show n ++ " " ++ w ++ (if n == 1 then "" else "s")

-- | A JSON array of objects with the fields @severity@, @code@, @line@,
--   @column@ and @message@.
renderJson :: [Diagnostic] -> String
renderJson ds = "[" ++ intercalate ",\n " (map one ds) ++ "]\n"
  where
    one d = "{\"severity\":" ++ str (severityWord (dSeverity d))
         ++ ",\"code\":" ++ str (dCode d)
         ++ ",\"line\":" ++ show (posLine (dPos d))
         ++ ",\"column\":" ++ show (posCol (dPos d))
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
