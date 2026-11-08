-- | Command line: @sldcheck TREE.sld PROGRAM.pl [--json] [--require-answers]@.
--
-- Exit status: 0 = no errors (warnings may be printed), 1 = the tree has
-- errors, 2 = bad input or usage (including syntax errors).
module Main (main) where

import System.Environment (getArgs)
import System.Exit
import System.IO

import SLDCheck.Check
import SLDCheck.Diagnostic
import SLDCheck.Notation

usage :: String
usage = unlines
  [ "usage: sldcheck TREE.sld PROGRAM.pl [--json] [--require-answers]"
  , ""
  , "  Checks an SLD tree against a Prolog program and reports every problem found."
  , "  --json             print the diagnostics as JSON"
  , "  --require-answers  a proven node without its answer is an error, not a warning" ]

data Opts = Opts { oTree :: FilePath, oProg :: FilePath, oJson :: Bool, oRequire :: Bool }

parseArgs :: [String] -> Either String Opts
parseArgs = go [] False False
  where
    go pos j r as = case as of
      []                     -> finish (reverse pos) j r
      "--json" : rest        -> go pos True r rest
      "--require-answers" : rest -> go pos j True rest
      a : _ | take 1 a == "-" -> Left ("unknown option " ++ a)
      a : rest               -> go (a : pos) j r rest
    finish [t, p] j r = Right (Opts t p j r)
    finish _ _ _      = Left "expected TREE.sld and PROGRAM.pl"

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Left e     -> hPutStr stderr (e ++ "\n" ++ usage) >> exitWith (ExitFailure 2)
    Right opts -> run opts

run :: Opts -> IO ()
run o = do
  progSrc <- readFile (oProg o)
  (prog, ops) <- either (die' . ("program: " ++)) pure (loadProgram (oProg o) progSrc)
  treeSrc <- readFile (oTree o)
  forest <- either (die' . show) pure (parseForestWith ops (oTree o) treeSrc)
  let ds = checkForest ((defaultOptions prog) { optRequireAnswers = oRequire o }) forest
  putStr (if oJson o then renderJson ds else renderText (oTree o) ds)
  exitWith (if hasErrors ds then ExitFailure 1 else ExitSuccess)
  where die' msg = hPutStrLn stderr msg >> exitWith (ExitFailure 2)
