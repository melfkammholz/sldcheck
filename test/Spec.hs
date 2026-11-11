-- | Tests of the checker.  Each case is a program, a tree and the error
--   codes the checker must report.  The reference solver is also compared
--   with SWI-Prolog when that is installed.
module Main (main) where

import Control.Exception (finally)
import Control.Monad
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, nub, sort, tails)
import System.Directory
import System.Exit
import System.FilePath ((</>))
import System.IO
import System.Process (readProcessWithExitCode)

import SLDCheck.Check
import SLDCheck.Diagnostic
import SLDCheck.Logic (isVariant)
import SLDCheck.Notation
import SLDCheck.Prolog
import SLDCheck.Run
import SLDCheck.Solve
import SLDCheck.TreeJson
import SLDCheck.Tree (Pos(..))
import SLDCheck.Version (version)

--------------------------------------------------------------------------------
-- Running the checker

-- | The diagnostics, or the syntax error.
diagnostics :: Bool -> String -> String -> Either String [Diagnostic]
diagnostics requireAnswers prog tree = do
  (p, ops) <- loadProgram "program" prog
  forest   <- either (Left . show) Right (parseForestWith ops "tree" tree)
  pure (checkForest ((defaultOptions p) { optRequireAnswers = requireAnswers }) forest)

-- | The codes of the diagnostics of one severity.
codesOf :: Severity -> [Diagnostic] -> [String]
codesOf sev ds = nub (sort [dCode d | d <- ds, dSeverity d == sev])

-- | The error codes, or the syntax error.
codes :: String -> String -> Either String [String]
codes prog tree = codesOf Error <$> diagnostics False prog tree

data Expect
  = Exactly [String]      -- ^ these error codes and no others
  | Includes [String]     -- ^ at least these error codes
  | Clean [String]        -- ^ no errors, and at least these warning codes
  | Warns [String]        -- ^ at least these warning codes (errors are not looked at)
  | Required [String]     -- ^ with @--require-answers@: at least these error codes
  | SyntaxError

data Case = Case String String String Expect

runCase :: Case -> Maybe String
runCase (Case name prog tree expect) = case expect of
  Clean ws    -> viaDiagnostics False $ \ds ->
    if null (codesOf Error ds) && all (`elem` codesOf Warning ds) ws then Nothing
    else Just (name ++ ": expected no errors and the warnings " ++ show ws ++ ", got errors " ++ show (codesOf Error ds) ++ " and warnings " ++ show (codesOf Warning ds))
  Warns ws    -> viaDiagnostics False $ \ds ->
    if all (`elem` codesOf Warning ds) ws then Nothing
    else Just (name ++ ": expected the warnings " ++ show ws ++ ", got " ++ show (codesOf Warning ds))
  Required cs -> viaDiagnostics True $ \ds ->
    if all (`elem` codesOf Error ds) cs then Nothing
    else Just (name ++ ": with --require-answers expected " ++ show cs ++ ", got " ++ show (codesOf Error ds))
  _           -> plain
  where
    viaDiagnostics req k = either (\e -> Just (name ++ ": syntax error: " ++ e)) k (diagnostics req prog tree)
    plain = runPlain (Case name prog tree expect)

runPlain :: Case -> Maybe String
runPlain (Case name prog tree expect) = case (expect, codes prog tree) of
  (SyntaxError, Left _)            -> Nothing
  (SyntaxError, Right cs)          -> Just (name ++ ": expected a syntax error, got " ++ show cs)
  (_, Left e)                      -> Just (name ++ ": syntax error: " ++ e)
  (Exactly want, Right cs)
    | cs == sort want              -> Nothing
    | otherwise                    -> Just (name ++ ": expected exactly " ++ show want ++ ", got " ++ show cs)
  (Includes want, Right cs)
    | all (`elem` cs) want         -> Nothing
    | otherwise                    -> Just (name ++ ": expected at least " ++ show want ++ ", got " ++ show cs)
  _                                -> Just (name ++ ": test bug")

-- | Replace a piece of the text; the piece must be there.
replace :: String -> String -> String -> String
replace old new s
  | old `isInfixOf` s = go s
  | otherwise         = error ("test bug: " ++ show old ++ " is not in the tree")
  where
    go [] = []
    go t@(c : cs)
      | take n t == old = new ++ drop n t
      | otherwise       = c : go cs
    n = length old

--------------------------------------------------------------------------------
-- Programs and trees

progP :: String
progP = unlines
  [ "p(a)."
  , "p(b)."
  , "q(X) :- p(X)."
  , "r(X) :- p(X), !."
  , "n(X) :- \\+ p(X)." ]

treeQ :: String
treeQ = unlines
  [ "?- q(X)."
  , "  | q(X1) :- p(X1)."
  , "  | {X1 |-> X}"
  , "  ?- p(X)."
  , "    | p(a)."
  , "    | {X |-> a}"
  , "    ?- true.                    {X |-> a}"
  , "    | p(b)."
  , "    | {X |-> b}"
  , "    ?- true.                    {X |-> b}" ]

treeR :: String
treeR = unlines
  [ "?- r(X)."
  , "  | r(X1) :- p(X1), !."
  , "  | {X1 |-> X}"
  , "  ?- p(X), !."
  , "    | p(a)."
  , "    | {X |-> a}"
  , "    ?- !.                       @c"
  , "      | !"
  , "      ?- true.                  {X |-> a}"
  , "    | pruned p/1 #2             by @c" ]

treeNot :: String
treeNot = unlines
  [ "?- n(c)."
  , "  | n(X1) :- \\+ p(X1)."
  , "  | {X1 |-> c}"
  , "  ?- \\+ p(c)."
  , "    | \\+ @t"
  , "    ?- true.                    {}"
  , ""
  , "?- p(c).                        @t"
  , "  | no rule" ]

treeNotFails :: String
treeNotFails = unlines
  [ "?- n(a)."
  , "  | n(X1) :- \\+ p(X1)."
  , "  | {X1 |-> a}"
  , "  ?- \\+ p(a)."
  , "    | \\+ @t fails"
  , ""
  , "?- p(a).                        @t"
  , "  | p(a)."
  , "  ?- true." ]

-- | The cut example with the part below the first step written separately.
treeRefs :: String
treeRefs = unlines
  [ "?- r(X)."
  , "  | r(X1) :- p(X1), !."
  , "  | {X1 |-> X}"
  , "  ?- p(X), !."
  , "    | p(a)."
  , "    | {X |-> a}"
  , "    @rest"
  , "    | pruned p/1 #2             by @rest"
  , ""
  , "?- !.                           @rest"
  , "  | !"
  , "  ?- true.                      {X |-> a}" ]

-- | A program with a loop, for a negation the solver cannot decide.
progLoop :: String
progLoop = "loop :- loop.\nn :- \\+ loop.\n"

cases :: [Case]
cases =
  [ ok "plain tree"            progP treeQ
  , ok "cut"                   progP treeR
  , ok "negation succeeds"     progP treeNot
  , ok "negation fails"        progP treeNotFails

  -- branches
  , bad "missing branch"       progP (replace "    | p(b).\n    | {X |-> b}\n    ?- true.                    {X |-> b}\n" "" treeQ) ["E022"]
  , bad "clauses out of order" progP (unlines
      [ "?- q(X)."
      , "  | q(X1) :- p(X1)."
      , "  | {X1 |-> X}"
      , "  ?- p(X)."
      , "    | p(b)."
      , "    | {X |-> b}"
      , "    ?- true.                    {X |-> b}"
      , "    | p(a)."
      , "    | {X |-> a}"
      , "    ?- true.                    {X |-> a}" ]) ["E021"]
  , bad "branch without reason" progP (unlines
      [ "?- q(X)."
      , "  | q(X1) :- p(X1)."
      , "  | {X1 |-> X}"
      , "  ?- p(X)." ]) ["E025", "E022"]
  , bad "wrong reason: no rule" progP (unlines
      [ "?- q(X)."
      , "  | q(X1) :- p(X1)."
      , "  | {X1 |-> X}"
      , "  ?- p(X)."
      , "    | no rule" ]) ["E026"]
  , bad "wrong reason: fails"  progP (replace "?- p(X)." "?- p(X)." (unlines
      [ "?- q(X)."
      , "  | q(X1) :- p(X1)."
      , "  | {X1 |-> X}"
      , "  ?- p(X)."
      , "    | fails" ])) ["E026"]
  , bad "unknown rule"         progP (replace "| p(a)." "| p(c)." treeQ) ["E011", "E022"]
  , bad "step below a proven node" progP (treeQ ++ "      | p(a).\n") ["E027"]
  , bad "step without node"    progP "?- q(X).\n  | q(X1) :- p(X1).\n  | {X1 |-> X}\n" ["E029"]
  , bad "wrong kind of step"   progP (replace "| p(a)." "| !" treeQ) ["E024"]

  -- resolution
  , bad "not renamed apart"    progP (replace "| q(X1) :- p(X1).\n  | {X1 |-> X}" "| q(X) :- p(X)." treeQ) ["E012"]
  , bad "not a unifier"        progP (replace "{X1 |-> X}" "{X1 |-> b}" treeQ) ["E015"]
  , bad "not most general"     progP (replace "{X1 |-> X}" "{X1 |-> a, X |-> a}" treeQ) ["E016"]
  , bad "binds a foreign variable" progP (replace "{X1 |-> X}" "{X1 |-> X, Z |-> a}" treeQ) ["E017"]
  , bad "wrong resolvent"      progP (replace "?- p(X).\n" "?- p(Y).\n" treeQ) ["E020"]
  , bad "wrong predicate"      progP (replace "| q(X1) :- p(X1)." "| r(X1) :- p(X1), !." treeQ) ["E013"]
  , bad "anonymous variable"   progP (replace "?- q(X)." "?- q(_)." treeQ) ["E010"]

  -- answers
  , bad "answer on an open node" progP (replace "?- p(X).\n" "?- p(X).   {X |-> a}\n" treeQ) ["E006"]
  , bad "wrong answer"         progP (replace "?- true.                    {X |-> a}" "?- true.                    {X |-> b}" treeQ) ["E050"]

  -- cut
  , bad "pruned alternative not written" progP (replace "    | pruned p/1 #2             by @c\n" "" treeR) ["E022"]
  , bad "pruned alternative drawn" progP (replace "    | pruned p/1 #2             by @c" "    | p(b).\n    | {X |-> b}\n    ?- !.\n      | !\n      ?- true.                  {X |-> b}" treeR) ["E033"]
  , bad "pruned without a cut" progP (replace "    | p(b).\n    | {X |-> b}\n    ?- true.                    {X |-> b}" "    | pruned p/1 #2             by @c" treeQ) ["E030", "E002"]
  , bad "pruned by a node that is no cut" progP (replace "?- true.                  {X |-> a}" "?- true.                  @d\n      {X |-> a}" (replace "by @c" "by @d" treeR)) ["E031"]
  , bad "pruned by an unknown node" progP (replace "by @c" "by @zz" treeR) ["E002"]
  , bad "pruned: not an alternative" progP (replace "p/1 #2" "p/1 #3" treeR) ["E032", "E022"]
  , bad "pruned: wrong predicate" progP (replace "p/1 #2" "q/1 #1" treeR) ["E032"]
  , bad "name used twice"      progP (replace "?- true.                  {X |-> a}" "?- true.                  @c\n      {X |-> a}" treeR) ["E001"]

  -- negation
  , bad "negation outcome: succeeds" progP (replace "| \\+ @t\n    ?- true.                    {}" "| \\+ @t fails" treeNot) ["E041"]
  , bad "negation outcome: fails" progP (replace "| \\+ @t fails" "| \\+ @t\n    ?- true.                    {}" treeNotFails) ["E041"]
  , bad "negation without its tree" progP (unlines (take 7 (lines treeNot))) ["E002"]
  , bad "negation tree for another goal" progP (replace "?- p(c).                        @t" "?- p(d).                        @t" treeNot) ["E040"]
  , bad "tree nobody refers to" progP (treeQ ++ "\n?- p(a).    @x\n  | p(a).\n  ?- true.\n") ["E003"]
  , bad "tree without a name"  progP (treeQ ++ "\n?- p(a).\n  | p(a).\n  ?- true.\n") ["E004"]

  -- references between trees
  , ok  "reference"           progP treeRefs
  , bad "unknown reference"   progP (replace "@rest\n    | pruned" "@nowhere\n    | pruned" treeRefs) ["E002"]
  , bad "reference cycle"     progP (replace "  | !\n  ?- true.                      {X |-> a}" "  | !\n  @rest" treeRefs) ["E007"]
  , bad "tree used twice"     progP (replace "    | pruned p/1 #2             by @rest" "    | pruned p/1 #2             by @rest\n  | r(X2) :- p(X2), !.\n  | {X2 |-> X}\n  @rest" treeRefs) ["E005"]
  , bad "part and negation"   progP (replace "    ?- true.                    {}" "    @t" treeNot) ["E008"]
  , bad "wrong goal in a referenced tree" progP (replace "?- !.                           @rest" "?- p(X).                        @rest" treeRefs) ["E020"]
  , bad "unreferenced tree after a reference" progP (treeRefs ++ "\n?- p(a).    @x\n  | p(a).\n  ?- true.\n") ["E003"]

  -- more errors
  , bad "duplicate binding"    progP (replace "{X1 |-> X}" "{X1 |-> X, X1 |-> X}" treeQ) ["E018"]
  , bad "clause used twice"    progP (replace "    | p(b).\n    | {X |-> b}\n    ?- true.                    {X |-> b}" "    | p(a).\n    | {X |-> a}\n    ?- true.                    {X |-> a}" treeQ) ["E023", "E022"]
  , bad "substitution on a cut" progP (replace "      | !\n" "      | !\n      | {}\n" treeR) ["E028"]
  , bad "wrong answer after a built-in" "t(X) :- X = 1.\n" (unlines
      [ "?- t(Y)."
      , "  | t(X1) :- X1 = 1."
      , "  | {X1 |-> Y}"
      , "  ?- Y = 1."
      , "    | builtin"
      , "    | {Y |-> 1}"
      , "    ?- true.   {Y |-> 2}" ]) ["E050"]
  , bad "negation tree used twice" progP (unlines
      [ "?- \\+ p(c), \\+ p(c)."
      , "  | \\+ @t"
      , "  ?- \\+ p(c)."
      , "    | \\+ @t"
      , "    ?- true.                    {}"
      , ""
      , "?- p(c).                        @t"
      , "  | no rule" ]) ["E005"]
  , bad "negation names a node inside a tree" progP (replace "| \\+ @t\n" "| \\+ @n1\n" (replace "?- \\+ p(c).\n" "?- \\+ p(c).   @n1\n" treeNot)) ["E040"]
  , bad "negation tree contradicts the step" progP (replace "?- p(c).                        @t\n  | no rule" "?- p(c).                        @t\n  | p(a).\n  ?- true." treeNot) ["E042"]
  , bad "builtin fails but is drawn as a step" "t :- 1 > 2.\n" (unlines
      [ "?- t."
      , "  | t :- 1 > 2."
      , "  ?- 1 > 2."
      , "    | builtin"
      , "    ?- true." ]) ["E026"]
  , bad "builtin succeeds but is drawn as failing" "t :- 2 > 1.\n" (unlines
      [ "?- t."
      , "  | t :- 2 > 1."
      , "  ?- 2 > 1."
      , "    | builtin fails" ]) ["E026"]
  , bad "rule for another predicate's clause" progP (replace "| q(X1) :- p(X1)." "| q(X1) :- p(X1), p(X1)." treeQ) ["E011"]
  , bad "two cuts: the later one named" progP (unlines
      [ "?- s(X)."
      , "  | s(X1) :- p(X1), !, !."
      , "  | {X1 |-> X}"
      , "  ?- p(X), !, !."
      , "    | p(a)."
      , "    | {X |-> a}"
      , "    ?- !, !.                    @first"
      , "      | !"
      , "      ?- !.                     @second"
      , "        | !"
      , "        ?- true.                {X |-> a}"
      , "    | pruned p/1 #2             by @second" ]) ["E031"]

  -- warnings
  , Case "answer not stated"   progP (replace "?- true.                    {X |-> a}" "?- true." treeQ) (Clean ["W004"])
  , Case "answer required"     progP (replace "?- true.                    {X |-> a}" "?- true." treeQ) (Required ["E051"])
  , Case "binding that does nothing" progP (replace "{X1 |-> X}" "{X1 |-> X, X |-> X}" treeQ) (Clean ["W005"])
  , Case "predicate without clauses" progP "?- z(1).\n  | no rule\n" (Clean ["W002"])
  , Case "control construct"   progP "?- (p(a) ; p(b)).\n" (Clean ["W001"])
  , Case "built-in raises an error" progP "?- X > 1.\n" (Clean ["W003"])
  , Case "negation the solver cannot decide" progLoop "?- n.\n  | n :- \\+ loop.\n  ?- \\+ loop.\n    | \\+ @t\n    ?- true.\n\n?- loop.   @t\n  | loop :- loop.\n  ?- loop.\n    | fails\n" (Warns ["W006"])

  -- syntax
  , Case "reference not aligned" progP "?- q(X).\n  | q(X1) :- p(X1).\n   @rest\n" SyntaxError
  , Case "answer without braces closed" progP "?- q(X).\n  | q(X1) :- p(X1).\n  | {X1 |-> X\n" SyntaxError
  , Case "missing end dot"  progP "?- q(X)\n  | q(X1) :- p(X1).\n" SyntaxError
  , Case "misaligned step"  progP "?- q(X).\n  | q(X1) :- p(X1).\n   | {X1 |-> X}\n" SyntaxError
  , Case "unknown step"     progP "?- q(X).\n  | pruned\n" SyntaxError
  , Case "empty file"       progP "" SyntaxError
  ]
  where
    ok n p t        = Case n p t (Exactly [])
    bad n p t cs    = Case n p t (Includes cs)

-- | Every @examples/NAME.sld@ with a @NAME.pl@ must be free of errors, except
--   the @NAME-broken.sld@ files (see 'brokenExample').
exampleCases :: IO [Maybe String]
exampleCases = do
  files <- listDirectory "examples"
  forM [f | f <- sort files, takeExtension' f == ".sld", not ("-broken.sld" `isSuffixOf` f)] $ \f -> do
    let base = take (length f - 4) f
    own <- doesFileExist ("examples" </> base ++ ".pl")
    -- NAME-variant.sld uses the program of NAME
    prog <- readFile ("examples" </> (if own then base else takeWhile (/= '-') base) ++ ".pl")
    tree <- readFile ("examples" </> f)
    pure $ case codes prog tree of
      Right [] -> Nothing
      other    -> Just ("examples/" ++ f ++ ": " ++ show other)
  where takeExtension' f = dropWhile (/= '.') f

-- | @examples/ancestor-broken.sld@ has five marked mistakes.  The checker must
--   report exactly those, one diagnostic each: a mistake must not make the
--   branch below it look wrong as well.
brokenExample :: IO (Maybe String)
brokenExample = do
  prog <- readFile "examples/ancestor.pl"
  tree <- readFile "examples/ancestor-broken.sld"
  pure $ case loadProgram "program" prog of
    Left e -> Just e
    Right (p, ops) -> case parseForestWith ops "tree" tree of
      Left e -> Just (show e)
      Right forest ->
        let errs = sort [dCode d | d <- checkForest (defaultOptions p) forest, dSeverity d == Error]
            want = ["E012", "E015", "E020", "E022", "E050"]
        in if errs == want then Nothing
           else Just ("examples/ancestor-broken.sld: expected " ++ show want ++ ", got " ++ show errs)

-- | Syntax errors are reported where the problem is, as diagnostics.
syntaxCases :: [(String, Maybe String)]
syntaxCases =
  [ at "a brace that is never closed" "?- p.\n  | q(X1) :- r.\n  | {X1 |-> a\n  ?- r.\n" (3, 5) "never closed"
  , at "a goal without its end dot" "?- p(X)\n  | q.\n" (1, 8) "end dot"
  , at "a rule without its end dot" "?- p.\n  | q :- r\n  ?- r.\n" (2, 11) "of the rule"
  , at "a tab in the indentation" "?- p.\n\t| q.\n" (2, 1) "tabs"
  , at "a tab after spaces" "?- p.\n  \t| q.\n" (2, 3) "tabs"
  , at "a step that is not aligned" "?- p.\n  | q.\n   | {X |-> a}\n" (3, 4) "not aligned"
  , ("only the syntax, not the semantics", check "a semantic error is not a syntax error" (analyse (SyntaxOnly Nothing (Input "t.sld" "?- q(X).\n"))) [])
  , ("a syntax error in the program", programError)
  , ("every diagnostic ends somewhere", ends)
  , ("a percent sign in quotes is no comment", quotedPercent)
  , ("the json says where and in which file", json)
  ]
  where
    at name tree (l, c) fragment = (name, case analyse (SyntaxOnly Nothing (Input "t.sld" tree)) of
      [d] | dCode d == "S001", dRole d == InTree, dPos d == Pos l c, fragment `isInfixOf` dMessage d -> Nothing
      ds -> Just ("expected S001 at " ++ show (l, c) ++ " about " ++ show fragment ++ ", got " ++ show ds))
    check what ds want = if map dCode ds == want then Nothing else Just (what ++ ": " ++ show ds)
    programError = case analyse (CheckTree False False (Input "p.pl" "p(a\n") (Input "t.sld" "?- p(a).\n")) of
      [d] | dCode d == "S002", dRole d == InProgram -> Nothing
      ds -> Just (show ds)
    ends = case analyse (CheckTree False False (Input "p.pl" "p(a).\n") (Input "t.sld" "?- p(a).  % the query\n")) of
      ds@(_ : _) | all (\d -> dEnd d == Just (Pos 1 9)) ds -> Nothing
      ds -> Just (show [(dCode d, dPos d, dEnd d) | d <- ds])
    quotedPercent = case analyse (CheckTree False False (Input "p.pl" "p('100%').\n") (Input "t.sld" "?- p('100%').\n")) of
      ds@(_ : _) | all (\d -> dEnd d == Just (Pos 1 14)) ds -> Nothing
      ds -> Just (show [(dCode d, dEnd d) | d <- ds])
    json =
      let ds = analyse (SyntaxOnly Nothing (Input "t.sld" "?- p(X)\n"))
          out = renderJson (Files "t.sld" Nothing) ds
          wanted = ["\"version\":\"" ++ version ++ "\"", "\"diagnostics\":[", "\"code\":\"S001\"", "\"file\":\"t.sld\"", "\"line\":1,\"column\":8,\"endLine\":1,\"endColumn\":9"]
      in case filter (not . (`isInfixOf` out)) wanted of
           []   -> Nothing
           miss -> Just (show miss ++ " missing from " ++ out)

-- | @--tree@: the tree as JSON.
treeOutput :: String -> String -> String -> String
treeOutput name prog tree =
  let (ds, result) = readTree (if null prog then Nothing else Just (Input "p.pl" prog)) (Input name tree)
  in renderTree (Files name Nothing) (maybe defaultOps fst result) (snd <$> result) ds

count :: String -> String -> Int
count needle = length . filter (needle `isPrefixOf`) . tails

treeCases :: IO [Maybe String]
treeCases = do
  member  <- readFile "examples/member.sld"
  memberP <- readFile "examples/member.pl"
  nested  <- readFile "examples/ancestor.sld"
  split   <- readFile "examples/ancestor-split.sld"
  ancP    <- readFile "examples/ancestor.pl"
  neg     <- readFile "examples/negation.sld"
  negP    <- readFile "examples/negation.pl"
  cut     <- readFile "examples/cut.sld"
  cutP    <- readFile "examples/cut.pl"
  let has what out needle = if needle `isInfixOf` out then Nothing else Just (what ++ ": " ++ show needle ++ " is not in " ++ out)
      m = treeOutput "member.sld" memberP member
      n = treeOutput "negation.sld" negP neg
      c = treeOutput "cut.sld" cutP cut
      nestedOut = treeOutput "ancestor.sld" ancP nested
      splitOut  = treeOutput "ancestor-split.sld" ancP split
  pure $
    [ has "rule" m "\"kind\":\"resolve\",\"rule\":\"member(X1, [X1|_1])\",\"clause\":1"
    , has "rule number" m "\"clause\":2"
    , has "built-in" m "\"kind\":\"builtin\",\"subst\":[{\"var\":\"Y\",\"term\":\"2\"}]"
    , has "answer" m "\"answer\":[{\"var\":\"X\",\"term\":\"1\"},{\"var\":\"Y\",\"term\":\"2\"}]"
    , has "goal" m "\"goal\":\"member(X, [1, 2]), Y is X + 1\""
    , has "position" m "\"line\":3,\"column\":3,\"kind\":\"resolve\""
    , has "no rule" m "\"kind\":\"no-rule\""
    , has "negation" n "\"kind\":\"negation-fails\",\"tree\":\"t1\""
    , has "negation trees" n "\"negations\":[{"
    , has "name of a negation tree" n "\"name\":\"t2\""
    , has "pruned" c "\"kind\":\"pruned\",\"predicate\":\"parent/2\",\"clause\":2,\"by\":\"c\""
    , has "cut" c "\"kind\":\"cut\""
    , has "no diagnostics" m "\"diagnostics\":[]"
    , if count "\"goal\":" nestedOut == count "\"goal\":" splitOut && count "\"goal\":" splitOut == 15 && "\"negations\":[]" `isInfixOf` splitOut
        then Nothing else Just "a tree split into parts has the same nodes as the nested one"
    , has "a syntax error" (treeOutput "t.sld" "" "?- p(X)\n") "\"tree\":null"
    , has "its diagnostic" (treeOutput "t.sld" "" "?- p(X)\n") "\"code\":\"S001\""
    , has "a reference to nowhere" (treeOutput "t.sld" "" "?- p.\n  | q.\n  @nowhere\n") "\"code\":\"E002\""
    , has "and the step keeps it" (treeOutput "t.sld" "" "?- p.\n  | q.\n  @nowhere\n") "\"ref\":\"nowhere\""
    ]

-- | The version of the program is the version of the package.
versionMatches :: IO (Maybe String)
versionMatches = do
  cabal <- readFile "sldcheck.cabal"
  let declared = [unwords (drop 1 (words l)) | l <- lines cabal, take 8 l == "version:"]
  pure (if declared == [version] then Nothing else Just ("sldcheck.cabal says " ++ show declared ++ ", SLDCheck.Version says " ++ show version))

--------------------------------------------------------------------------------
-- The solver against SWI-Prolog

solverCases :: [(String, String, String)]
solverCases =
  [ ("ancestor", ancestor, "ancestor(tom, W)")
  , ("ancestor all", ancestor, "ancestor(X, Y)")
  , ("cut in the body", progP, "r(X)")
  , ("cut and backtracking", cutProg, "d(X, Y)")
  , ("max", cutProg, "max(3, 5, M)")
  , ("max, second clause", cutProg, "max(5, 3, M)")
  , ("negation holds", progP, "n(c)")
  , ("negation fails", progP, "n(a)")
  , ("negation as a filter", cutProg, "b(X), \\+ c(X)")
  , ("arithmetic", cutProg, "b(X), X > 1, Y is X * 2")
  , ("lists", "member(X, [X|_]).\nmember(X, [_|T]) :- member(X, T).\n", "member(X, [1, 2]), Y is X + 1")
  , ("cut inside negation", cutProg, "\\+ (b(X), !, c(X))")
  ]
  where
    ancestor = "parent(tom, bob).\nparent(bob, ann).\nparent(bob, pat).\nancestor(X, Y) :- parent(X, Y).\nancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).\n"
    cutProg = unlines
      [ "b(1). b(2). b(3)."
      , "c(2). c(3)."
      , "d(X, Y) :- b(X), !, c(Y)."
      , "max(X, Y, Y) :- X =< Y, !."
      , "max(X, _, X)." ]

swiAnswers :: String -> String -> IO (Maybe [[Term]])
swiAnswers prog query = do
  tmp <- getTemporaryDirectory
  let file = tmp </> "sldcheck-spec-program.pl"
  writeFile file prog
  qt <- either (fail . show) pure (parseTerm query)
  let vars = termVarsOf qt
      listText = "[" ++ concatMap id (zipWith (\i v -> (if i > (0 :: Int) then "," else "") ++ v) [0 ..] vars) ++ "]"
      goal = "forall((" ++ query ++ "), (write_term(" ++ listText ++ ", [quoted(true)]), nl))"
  (code, out, _) <- readProcessWithExitCode "swipl" ["-q", "-g", goal, "-t", "halt", file] ""
  removeFile file `finally` pure ()
  case code of
    ExitSuccess -> pure (Just [ xs | l <- lines out, Right t <- [parseTerm l], Just xs <- [asList t] ])
    _           -> pure Nothing
  where
    asList (List xs Nothing) = Just xs
    asList (Atom "[]")       = Just []
    asList _                 = Nothing

termVarsOf :: Term -> [String]
termVarsOf = nub . go
  where
    go (Var v)         = [v]
    go (Compound _ as) = concatMap go as
    go (List xs tl)    = concatMap go xs ++ maybe [] go tl
    go _               = []

runSolverCase :: (String, String, String) -> IO (Maybe String)
runSolverCase (name, prog, query) = do
  p <- either fail (pure . fst) (loadProgram "program" prog)
  q' <- either (fail . show) pure (parseTerm query)
  mswi <- swiAnswers prog query
  let Result mine complete = solveQuery p q' 100000
  pure $ case mswi of
    Nothing -> Just (name ++ ": swipl failed")
    Just swi
      | not complete -> Just (name ++ ": the solver did not finish")
      | length swi == length mine && and (zipWith same swi mine) -> Nothing
      | otherwise -> Just (name ++ ": swipl gives " ++ show swi ++ " but the solver gives " ++ show mine)
  where
    same a b = isVariant (Compound "ans" a) (Compound "ans" b)

--------------------------------------------------------------------------------

-- | Cases run with anonymous variables allowed: program, tree, error codes.
anonCases :: [(String, String, String, [String])]
anonCases =
  [ ("_ in a rule needs no binding", "p(a, _).\n", "?- p(X, Y).\n  | p(a, _).\n  | {X |-> a}\n  ?- true.                      {X |-> a}\n", [])
  , ("_ in a rule, wrong answer", "p(a, _).\n", "?- p(X, Y).\n  | p(a, _).\n  | {X |-> a}\n  ?- true.                      {X |-> a, Y |-> b}\n", ["E050"])
  , ("_ in the query", "p(a, _).\np(c, _).\n", "?- p(X, _).\n  | p(a, _).\n  | {X |-> a}\n  ?- true.                      {X |-> a}\n  | p(c, _).\n  | {X |-> c}\n  ?- true.                      {X |-> c}\n", [])
  , ("_ in a goal below", "q(X) :- p(X, Y), r(Y).\np(a, b).\nr(b).\n", unlines
      [ "?- q(X)."
      , "  | q(X1) :- p(X1, Y1), r(Y1)."
      , "  | {X1 |-> X}"
      , "  ?- p(X, _), r(_)."
      , "    | p(a, b)."
      , "    | {X |-> a, Y1 |-> b}"
      , "    ?- r(b)."
      , "      | r(b)."
      , "      | {}"
      , "      ?- true.                  {X |-> a}" ], [])
  , ("_ stands for the wrong term", "p(a).\nq(X) :- p(X).\n", "?- q(X).\n  | q(X1) :- p(X1).\n  | {X1 |-> X}\n  ?- r(_).\n", ["E020", "E022", "E025"])
  ]

anonCase :: (String, String, String, [String]) -> Maybe String
anonCase (name, prog, tree, want) = case loadProgram "program" prog of
  Left e -> Just (name ++ ": " ++ e)
  Right (p, ops) -> case parseForestWith ops "tree" tree of
    Left e -> Just (name ++ ": syntax error: " ++ show e)
    Right forest ->
      let got = codesOf Error (checkForest ((defaultOptions p) { optAllowAnonymous = True }) forest)
      in if got == sort want then Nothing else Just (name ++ ": expected " ++ show want ++ ", got " ++ show got)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  let failures = [m | Just m <- map runCase cases]
  mapM_ putStrLn failures
  putStrLn (show (length cases - length failures) ++ "/" ++ show (length cases) ++ " checker cases passed")

  exampleResults <- exampleCases
  let exampleFailures = [m | Just m <- exampleResults]
  mapM_ putStrLn exampleFailures
  putStrLn (show (length exampleResults - length exampleFailures) ++ "/" ++ show (length exampleResults) ++ " example files are correct")

  let syntaxFailures = [name ++ ": " ++ m | (name, Just m) <- syntaxCases]
  mapM_ putStrLn syntaxFailures
  putStrLn (show (length syntaxCases - length syntaxFailures) ++ "/" ++ show (length syntaxCases) ++ " syntax error cases are located right")
  let anonFailures = [m | Just m <- map anonCase anonCases]
  mapM_ putStrLn anonFailures
  putStrLn (show (length anonCases - length anonFailures) ++ "/" ++ show (length anonCases) ++ " anonymous variable cases pass")
  treeProblems <- treeCases
  let treeFailures = [m | Just m <- treeProblems]
  mapM_ putStrLn treeFailures
  putStrLn (show (length treeProblems - length treeFailures) ++ "/" ++ show (length treeProblems) ++ " checks of the tree output pass")
  versionProblem <- versionMatches
  mapM_ putStrLn versionProblem

  broken <- brokenExample
  mapM_ putStrLn broken
  putStrLn (maybe "the broken example reports its five mistakes and nothing else" (const "the broken example is wrong") broken)

  hasSwipl <- findExecutable "swipl"
  solverFailures <- case hasSwipl of
    Nothing -> putStrLn "swipl not found: solver cases skipped" >> pure []
    Just _  -> do
      rs <- mapM runSolverCase solverCases
      let fs = [m | Just m <- rs]
      mapM_ putStrLn fs
      putStrLn (show (length solverCases - length fs) ++ "/" ++ show (length solverCases) ++ " solver cases agree with swipl")
      pure fs
  when (not (null anonFailures)) exitFailure
  when (not (null failures && null exampleFailures && null solverFailures) || broken /= Nothing || not (null syntaxFailures) || not (null treeFailures) || versionProblem /= Nothing) exitFailure
