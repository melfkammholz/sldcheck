-- | The version of sldcheck, as @--version@ and the JSON output report it.
--   Keep it equal to @version:@ in @sldcheck.cabal@ (the tests check that).
module SLDCheck.Version (version) where

version :: String
version = "0.2.0.0"
