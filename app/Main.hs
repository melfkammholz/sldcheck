-- | Command line: see 'usage'.
--
-- Exit status: 0 = no errors (warnings may be printed), 1 = the tree has
-- errors, 2 = bad input or usage (including syntax errors in the tree or the program).
module Main (main) where

import Control.Exception (IOException, try)
import System.Environment (getArgs)
import System.Exit
import System.IO

import SLDCheck.Diagnostic
import SLDCheck.Prolog (defaultOps)
import SLDCheck.Run
import SLDCheck.TreeJson
import SLDCheck.Version (version)

usage :: String
usage = unlines
  [ "usage: sldcheck [--json] [--require-answers] TREE.sld PROGRAM.pl"
  , "       sldcheck --syntax [--json] TREE.sld [PROGRAM.pl]"
  , "       sldcheck --tree TREE.sld [PROGRAM.pl]"
  , "       sldcheck --version"
  , ""
  , "  Checks an SLD tree against a Prolog program and reports every problem found."
  , "  TREE.sld can be - for standard input."
  , ""
  , "  --json             print the diagnostics as a JSON object"
  , "  --require-answers  a proven node without its answer is an error, not a warning"
  , "  --syntax           only read the tree, which is much quicker; the program is only"
  , "                     needed if it declares operators the tree uses"
  , "  --tree             print the tree as JSON, for drawing it (see README.md)"
  , "  --version          print the version"
  , ""
  , "  Exit status: 0 no errors, 1 the tree has errors, 2 bad input (a syntax error"
  , "  in the tree or the program is reported like any other problem)." ]

data Opts = Opts
  { oFiles   :: [FilePath]
  , oJson    :: Bool
  , oRequire :: Bool
  , oSyntax  :: Bool
  , oTree    :: Bool
  }

data Command = Version | Help | Run Opts

parseArgs :: [String] -> Either String Command
parseArgs = go (Opts [] False False False False)
  where
    go o as = case as of
      []                         -> Right (Run o { oFiles = reverse (oFiles o) })
      "--version" : _            -> Right Version
      "--help" : _               -> Right Help
      "-h" : _                   -> Right Help
      "--json" : rest            -> go o { oJson = True } rest
      "--require-answers" : rest -> go o { oRequire = True } rest
      "--syntax" : rest          -> go o { oSyntax = True } rest
      "--tree" : rest            -> go o { oTree = True } rest
      a : _ | take 1 a == "-" && a /= "-" -> Left ("unknown option " ++ a)
      a : rest                   -> go o { oFiles = a : oFiles o } rest

main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  args <- getArgs
  case parseArgs args of
    Left e         -> hPutStr stderr (e ++ "\n" ++ usage) >> exitWith (ExitFailure 2)
    Right Version  -> putStrLn ("sldcheck " ++ version)
    Right Help     -> putStr usage
    Right (Run o)  -> run o

run :: Opts -> IO ()
run o = case (oSyntax o || oTree o, oFiles o) of
  (False, [t, p]) -> go (Just p) t
  (True,  [t])    -> go Nothing t
  (True,  [t, p]) -> go (Just p) t
  (False, _)      -> usageError "expected TREE.sld and PROGRAM.pl"
  (True,  _)      -> usageError "expected TREE.sld and, if you like, PROGRAM.pl"
  where
    usageError e = hPutStr stderr (e ++ "\n" ++ usage) >> exitWith (ExitFailure 2)
    go mprog tree = do
      prog <- traverse (\p -> Input p <$> readUtf8 p) mprog
      treeText <- if tree == "-" then hSetEncoding stdin utf8 >> getContents else readUtf8 tree
      let treeIn = Input (if tree == "-" then "<stdin>" else tree) treeText
      if oTree o then showTree prog treeIn else check prog treeIn
    check prog treeIn = do
      let job = case (oSyntax o, prog) of
            (False, Just p) -> CheckTree (oRequire o) p treeIn
            (_, p)          -> SyntaxOnly p treeIn
          ds = analyse job
          files = Files (inputName treeIn) (inputName <$> prog)
      putStr (if oJson o then renderJson files ds else renderText files ds)
      exitWith $ if any isSyntaxError ds then ExitFailure 2
                 else if hasErrors ds then ExitFailure 1 else ExitSuccess
    showTree prog treeIn = do
      let (ds, result) = readTree prog treeIn
          files = Files (inputName treeIn) (inputName <$> prog)
      putStr (renderTree files (maybe defaultOps fst result) (snd <$> result) ds)
      exitWith (if any isSyntaxError ds then ExitFailure 2 else ExitSuccess)

-- | Text files are UTF-8, whatever the locale says.
readUtf8 :: FilePath -> IO String
readUtf8 path = do
  r <- try (openFile path ReadMode) :: IO (Either IOException Handle)
  case r of
    Left e  -> hPutStrLn stderr (path ++ ": " ++ show e) >> exitWith (ExitFailure 2)
    Right h -> do
      hSetEncoding h utf8
      s <- hGetContents h
      length s `seq` hClose h
      pure s
