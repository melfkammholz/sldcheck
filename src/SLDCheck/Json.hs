-- | Just enough JSON to print what sldcheck reports.
module SLDCheck.Json
  ( Value(..)
  , render
  ) where

import Data.Char (ord)
import Data.List (intercalate)
import Numeric (showHex)

data Value
  = Null
  | Num Int
  | Str String
  | Arr [Value]
  | Obj [(String, Value)]

-- | Compact, on one line.
render :: Value -> String
render v = case v of
  Null    -> "null"
  Num n   -> show n
  Str s   -> str s
  Arr xs  -> "[" ++ intercalate "," (map render xs) ++ "]"
  Obj kvs -> "{" ++ intercalate "," [str k ++ ":" ++ render x | (k, x) <- kvs] ++ "}"
  where
    str s = "\"" ++ concatMap esc s ++ "\""
    esc c = case c of
      '"'  -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\t' -> "\\t"
      _ | ord c < 0x20 -> "\\u" ++ replicate (4 - length h) '0' ++ h
        | otherwise    -> [c]
      where h = showHex (ord c) ""
