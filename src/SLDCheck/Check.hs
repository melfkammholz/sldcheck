-- | The checker: finds what is wrong in an SLD tree for a Prolog program.
--
-- Every node is checked against what is correct /from that node as it is
-- drawn/, not against an ideal tree.  A mistake in one step therefore does
-- not hide or cause mistakes elsewhere, and as many problems as possible are
-- reported in one run.
--
-- What is checked, with the code of the diagnostic:
--
-- * __Structure__: names are unique (E001), referenced names exist (E002),
--   every tree after the first is the tree of exactly one negation (E003,
--   E004, E005), answers only on proven nodes (E006).
-- * __Variables__: no anonymous variable @_@, which no substitution could bind
--   (E010); rules are renamed apart from everything used before (E012).
-- * __Resolution__: the rule is a renamed copy of a clause of the selected
--   literal's predicate (E011, E013), the substitution is a most general
--   unifier (E014 to E018), the child goal is the resolvent (E020).
-- * __Branches__: clauses appear in program order (E021), every clause whose
--   head unifies is drawn or pruned (E022), at most once (E023), and nothing
--   else is a step of this node (E024).  A branch must end in a stated reason
--   (E025) that is the true one (E026), a proven node has no steps (E027), a
--   built-in binds what it binds (E028), a step has its child (E029).
-- * __Cut__: a pruned alternative really is pruned (E030) by the cut that
--   prunes it (E031), is an alternative at all (E032), and an alternative
--   that is pruned is not drawn (E033).
-- * __Negation__: the tree is for the negated goal (E040), the outcome is the
--   true one (E041) and agrees with the tree (E042).
-- * __Answers__: the stated answer is the composed substitution of the branch
--   restricted to the query variables (E050), and is there (E051/W004).
module SLDCheck.Check
  ( Options(..)
  , defaultOptions
  , checkForest
  , loadProgram
  ) where

import Control.Monad
import Control.Monad.Writer.Strict
import Data.List (intercalate, nub, sort, (\\))
import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Data.Set as S
import Text.Parsec (SourceName)

import SLDCheck.Diagnostic
import SLDCheck.Expand
import SLDCheck.Logic
import SLDCheck.Prolog
import SLDCheck.Solve
import SLDCheck.Tree

data Options = Options
  { optProgram        :: Program
  , optBudget         :: Int     -- ^ steps the reference solver may take
  , optRequireAnswers :: Bool    -- ^ is a success node without its answer an error?
  }

defaultOptions :: Program -> Options
defaultOptions p = Options p 200000 False

-- | Read a program; the operator table at its end is for reading the tree.
loadProgram :: SourceName -> String -> Either String (Program, OpTable)
loadProgram name src = either (Left . show) Right (parseProgramOps name src)

--------------------------------------------------------------------------------
-- Annotated trees

-- | A node with what the cut needs: its depth, and, if its selected literal
--   is a cut, the depth of the node whose clause the cut belongs to.
data ANode = ANode
  { aN     :: Node
  , aDepth :: Int
  , aCut   :: Maybe Int
  , aSteps :: [AStep]
  }

data AStep = AStep { aS :: Step, aChild :: Maybe ANode }

-- | Every literal of a goal remembers the depth of the node that called the
--   clause it came from (the query's literals: the root).  A cut selected at
--   a node removes the alternatives of that node and all nodes below it on
--   the path to the cut.
annotate :: Node -> ANode
annotate root = go 0 (replicate (length (litsOf root)) 0) root
  where
    litsOf = goalLits . toCore . nodeGoal
    go d tags0 n = ANode n d cutDepth [AStep s (child s <$> stepChild s) | s <- nodeSteps n]
      where
        tags     = fitEnd (length (litsOf n)) tags0
        cutDepth = case (litsOf n, tags) of
          (Atom "!" : _, t : _) -> Just t
          _                     -> Nothing
        child s c = go (d + 1) (fitEnd (length (litsOf c)) (new s ++ drop 1 tags)) c
        new s = case stepKind s of
          Resolve r -> replicate (length (snd (splitClause (toCore r)))) d
          _         -> []

-- | Make a list exactly @m@ long, keeping the end (the rest of a goal).
fitEnd :: Int -> [Int] -> [Int]
fitEnd m xs
  | length xs >= m = drop (length xs - m) xs
  | otherwise      = replicate (m - length xs) (headOr xs) ++ xs
  where headOr (x : _) = x
        headOr []      = 0

preorder :: ANode -> [ANode]
preorder n = n : concat [preorder c | AStep { aChild = Just c } <- aSteps n]

-- | The first cut, in the order Prolog runs, among these trees whose cut
--   reaches a node at the given depth.
firstCutAbove :: Int -> [ANode] -> Maybe ANode
firstCutAbove d ts = listToMaybe [n | t <- ts, n <- preorder t, Just c <- [aCut n], c <= d]

--------------------------------------------------------------------------------
-- The checking monad

data Out = Out
  { oDiags   :: [Diagnostic]
  , oAnswers :: [[Term]]            -- ^ values of the query variables at each proven node
  , oRefs    :: [(String, Pos)]     -- ^ negation steps and the trees they name
  }

instance Semigroup Out where Out a b c <> Out a' b' c' = Out (a ++ a') (b ++ b') (c ++ c')
instance Monoid Out where mempty = Out [] [] []

type W = Writer Out

diag :: Severity -> String -> Pos -> String -> W ()
diag sev code pos msg = tell (Out [Diagnostic sev code pos msg] [] [])

err, warn :: String -> Pos -> String -> W ()
err  = diag Error
warn = diag Warning

data Env = Env
  { envProg    :: Program
  , envDb      :: M.Map Indicator [Clause]
  , envNames   :: M.Map String ANode       -- ^ every named node
  , envTrees   :: M.Map String ANode       -- ^ the roots of the trees after the first
  , envBudget  :: Int
  , envRequire :: Bool
  }

data Ctx = Ctx
  { cxUsed  :: S.Set String   -- ^ variables used so far on the path
  , cxAns   :: Sub            -- ^ each query variable with the substitutions of the path applied
  , cxQVars :: [String]
  }

--------------------------------------------------------------------------------
-- Entry point

-- | Check a parsed file against the program.
checkForest :: Options -> Forest -> [Diagnostic]
checkForest _ [] = []
checkForest opts forest0 = sortDiagnostics (nub (expansionProblems ++ oDiags out ++ final))
  where
    (forest, expansionProblems) = expandForest forest0
    (root, others) = case forest of
      r : os -> (r, os)
      []     -> error "checkForest: the forest was empty after expansion"
    amain    = annotate root
    aothers  = map annotate others
    allNodes = concatMap preorder (amain : aothers)
    named    = [(nm, a) | a <- allNodes, Just nm <- [nodeName (aN a)]]
    env = Env
      { envProg    = optProgram opts
      , envDb      = indexProgram (optProgram opts)
      , envNames   = M.fromListWith (\_ old -> old) named
      , envTrees   = M.fromList [(nm, a) | a <- aothers, Just nm <- [nodeName (aN a)]]
      , envBudget  = optBudget opts
      , envRequire = optRequireAnswers opts }

    -- the query's tree first: it says which trees the negations use
    mainOut = execWriter (walkTree env S.empty amain True)
    refs    = oRefs mainOut

    out = mainOut <> execWriter (structure >> mapM_ unreferenced aothers)

    structure = do
      forM_ (M.toList (M.fromListWith (flip (++)) [(nm, [nodePos (aN a)]) | (nm, a) <- named])) $ \(nm, ps) ->
        forM_ (zip ps (drop 1 ps)) $ \(first, p) ->
          err "E001" p ("the name @" ++ nm ++ " is already used at line " ++ show (posLine first))
      forM_ (M.toList (M.fromListWith (flip (++)) [(nm, [p]) | (nm, p) <- refs])) $ \(nm, ps) ->
        forM_ (zip ps (drop 1 ps)) $ \(first, p) ->
          err "E005" p ("the tree @" ++ nm ++ " is already the tree of the negation at line " ++ show (posLine first)
                        ++ "; every negation draws its own tree")

    -- a tree no negation refers to is still checked, on its own
    unreferenced a = case nodeName (aN a) of
      Nothing -> do
        err "E004" (nodePos (aN a)) "this tree has no name, so no negation can refer to it: write @name after its goal"
        walkTree env S.empty a False
      Just nm -> when (nm `notElem` map fst refs) $ do
        err "E003" (nodePos (aN a)) ("no negation refers to the tree @" ++ nm ++ " (write `| \\+ @" ++ nm ++ "` at the node that selects the negated goal)")
        walkTree env S.empty a False

    -- the safety net: with no errors found, the answers on the tree and the
    -- reference solver must agree
    final = if hasErrors (oDiags out) then [] else consistency
    consistency
      | not complete =
          [Diagnostic Info "I001" (nodePos root)
            "the reference solver stopped early (step limit, error or unsupported built-in), so the answers were not cross-checked"]
      | null extra && null absent = []
      | otherwise =
          [Diagnostic Error "E099" (nodePos root)
            ("the checker found no problems, but the tree's answers differ from the reference solver's (tree only: "
             ++ describeAnswers extra ++ "; solver only: " ++ describeAnswers absent ++ "). This is a bug in the checker.")]
      where
        Result ref complete = solveQuery (optProgram opts) (nodeGoal root) (optBudget opts)
        (extra, absent) = pairUp (oAnswers mainOut) ref
        qv = termVars (toCore (nodeGoal root))
        describeAnswers as = if null as then "none" else intercalate " / " (map (showAns qv) as)

-- | Check one tree.  The flag says whether its answers count (the query's
--   tree) or not (the tree of a negation).
walkTree :: Env -> S.Set String -> ANode -> Bool -> W ()
walkTree env used0 root countAnswers = body
  where
    goal  = toCore (nodeGoal (aN root))
    qv    = termVars goal
    cx    = Ctx (used0 `S.union` S.fromList qv) (M.fromList [(v, Var v) | v <- qv]) qv
    body | countAnswers = walk env cx root
         | otherwise    = censor (\o -> o { oAnswers = [] }) (walk env cx root)

--------------------------------------------------------------------------------
-- One node

walk :: Env -> Ctx -> ANode -> W ()
walk env cx an = do
  when (hasAnon goalT) $ anonymous pos
  when (not (null lits) && isJust (nodeAnswer n)) $
    err "E006" pos "an answer can only be stated at a proven node (goal `true`); this node still has goals left"
  case lits of
    []            -> success
    sel : rest
      | sel == Atom "!"            -> checkCut env cx an rest
      | Compound "\\+" [g] <- sel  -> checkNegation env cx an g rest
      | Just b <- builtinStep sel  -> checkBuiltin env cx an sel b rest
      | otherwise                  -> checkCall env cx an sel rest
  where
    n      = aN an
    pos    = nodePos n
    goalT  = toCore (nodeGoal n)
    lits   = goalLits goalT

    success = do
      forM_ (aSteps an) $ \st ->
        err "E027" (stepPos (aS st)) "this node has the empty goal: the query is proven here and nothing can be derived from it"
      tell (Out [] [[cxAns cx M.! v | v <- cxQVars cx]] [])
      let expected = M.filterWithKey (\v t -> t /= Var v) (cxAns cx)
      case nodeAnswer n of
        Nothing
          | M.null expected -> pure ()
          | envRequire env  -> err "E051" pos ("the answer is missing: write " ++ showSub expected ++ " after the goal")
          | otherwise       -> warn "W004" pos ("the answer is not stated; it is " ++ showSub expected)
        Just stated -> do
          let given = M.filterWithKey (\v t -> t /= Var v) (M.fromList [(v, toCore t) | (v, t) <- stated])
          when (given /= expected) $
            err "E050" pos ("the answer " ++ showSub given ++ " is wrong: composing the substitutions on this branch and restricting them to the query variables gives "
                            ++ showSub expected)

anonymous :: Pos -> W ()
anonymous pos = err "E010" pos
  "the anonymous variable _ cannot be bound by a substitution: give it a name (_1, _G2, ...); the renamed rule needs a fresh name for it too"

hasAnon :: Term -> Bool
hasAnon t = case t of
  Var "_"       -> True
  Compound _ as -> any hasAnon as
  List xs tl    -> any hasAnon xs || maybe False hasAnon tl
  _             -> False

--------------------------------------------------------------------------------
-- Messages

q :: Term -> String
q t = "`" ++ showT t ++ "`"

qGoal :: [Term] -> String
qGoal = q . goalFromLits

describe :: StepKind -> String
describe k = case k of
  Resolve _        -> "a rule"
  Builtin          -> "`builtin`"
  CutStep          -> "`!`"
  Negation t       -> "`\\+ @" ++ t ++ "`"
  Pruned _ _ _     -> "`pruned`"
  NoRule           -> "`no rule`"
  BuiltinFails     -> "`builtin fails`"
  NegationFails t  -> "`\\+ @" ++ t ++ " fails`"
  Fails            -> "`fails`"

pind :: Indicator -> String
pind (f, n) = f ++ "/" ++ show n

nodeRef :: ANode -> String
nodeRef a = case nodeName (aN a) of
  Just nm -> "@" ++ nm ++ " (line " ++ show (posLine (nodePos (aN a))) ++ ")"
  Nothing -> "the cut at line " ++ show (posLine (nodePos (aN a))) ++ " (which has no name yet: write @name after its goal)"

--------------------------------------------------------------------------------
-- Substitutions and unification

toSub :: [(String, Term)] -> Sub
toSub bs = M.fromList [(v, toCore t) | (v, t) <- bs]

-- | An mgu that binds the variables of the second term (the rule head) in
--   preference, which is how a rule's fresh variables are usually bound.
unifyHead :: Term -> Term -> Maybe Sub
unifyHead a b = unifyPreferring (`elem` termVars (toCore b)) a b

-- | Is the substitution a most general unifier of the two terms?  Returns the
--   diagnostics and whether it is at least a unifier.
unifierReport :: Pos -> Term -> Term -> [(String, Term)] -> ([Diagnostic], Bool)
unifierReport pos a b bindings = (dups ++ trivial ++ extra ++ main, valid)
  where
    bs       = [(v, toCore t) | (v, t) <- bindings]
    theta    = M.fromList bs
    names    = map fst bs
    d sev c m = Diagnostic sev c pos m
    dups     = [ d Error "E018" ("the variable " ++ v ++ " is bound more than once in the substitution")
               | v <- nub (names \\ nub names) ]
    trivial  = [ d Warning "W005" ("the binding " ++ v ++ " |-> " ++ v ++ " does nothing")
               | (v, Var w) <- bs, v == w ]
    relevant = S.fromList (termVars a ++ termVars b)
    outside  = [v | v <- nub names, not (v `S.member` relevant)]
    extra    = [ d Error "E017" ("the substitution binds " ++ intercalate ", " outside ++ ", which "
                                 ++ (if length outside == 1 then "does" else "do") ++ " not occur in "
                                 ++ q a ++ " or " ++ q b ++ "; a most general unifier only binds variables of the two terms")
               | not (null outside) ]
    (main, valid) = case unifyHead a b of
      Nothing -> ([d Error "E014" (q a ++ " and " ++ q b ++ " do not unify, so this derivation step is impossible")], False)
      Just sigma ->
        let ta = applySub theta a
            tb = applySub theta b
        in if ta /= tb
             then ([d Error "E015" ("the substitution is not a unifier: it turns " ++ q a ++ " into " ++ q ta
                                    ++ " and " ++ q b ++ " into " ++ q tb ++ "; a most general unifier is " ++ showSub sigma)], False)
             else if not (isVariant ta (applySub sigma a))
               then ([d Error "E016" ("the substitution is a unifier but not a most general one (" ++ q ta
                                      ++ " is too specific); a most general unifier is " ++ showSub sigma)], True)
               else ([], True)

-- | The goal below a step must be the resolvent.  @theta@ is the drawn
--   substitution; if it is not even a unifier, the true mgu decides, up to
--   renaming.  When the goal is wrong, the right one is returned: the checker
--   goes on below the node as if it had been written, so that one mistake
--   does not make everything under it look wrong.
checkResolvent :: [Term] -> Sub -> Bool -> Maybe Sub -> ANode -> W (Maybe [Term])
checkResolvent new theta valid mgu child
  | ok        = pure Nothing
  | otherwise = do
      err "E020" (nodePos (aN child))
        ("wrong goal: it should be " ++ qGoal shown ++ ", but the node has " ++ qGoal actual ++ hint)
      pure (Just shown)
  where
    shown    = if valid then expected else fromMaybe expected (listToMaybe byMgu)
    actual   = goalLits (toCore (nodeGoal (aN child)))
    expected = map (applySub theta) new
    byMgu    = [map (applySub s) new | not valid, Just s <- [mgu]]
    ok | valid     = expected == actual
       | otherwise = any (\e -> length e == length actual && isVariant (Compound "g" e) (Compound "g" actual)) byMgu
    hint
      | map showT shown /= map showT actual
      , sort (map showT shown) == sort (map showT actual) =
          " (the same literals in a different order: the rule body replaces the selected literal in place)"
      | actual == new = " (the substitution has not been applied to the new goal)"
      | otherwise     = ""

-- | Go on below a step: the child must exist, its goal must be the resolvent
--   (@new@ with the substitution applied), and it is checked in turn.
descend :: Env -> Ctx -> AStep -> [Term] -> Sub -> [Term] -> Bool -> Maybe Sub -> W ()
descend env cx st rule theta new valid mgu = case aChild st of
  Nothing -> err "E029" (stepPos (aS st)) "this step has no node below it: write the goal that results from it, aligned with the step"
  Just c0 -> do
    repaired <- checkResolvent new theta valid mgu c0
    let c  = maybe c0 (\ls -> c0 { aN = (aN c0) { nodeGoal = goalFromLits ls } }) repaired
        cx' = cx { cxUsed = cxUsed cx `S.union` S.fromList (concatMap termVars rule ++ termVars (toCore (nodeGoal (aN c))))
                 , cxAns  = M.map (applySub theta) (cxAns cx) }
    walk env cx' c

noSubst :: AStep -> W ()
noSubst st = forM_ (stepSubst (aS st)) $ \_ ->
  err "E028" (stepPos (aS st)) ("a step of the kind " ++ describe (stepKind (aS st)) ++ " has no substitution: remove the { ... } line")

unexpected :: String -> (StepKind -> Bool) -> ANode -> W ()
unexpected why ok an = forM_ (aSteps an) $ \st ->
  unless (ok (stepKind (aS st))) $
    err "E024" (stepPos (aS st)) ("the step " ++ describe (stepKind (aS st)) ++ " does not fit here: " ++ why)

--------------------------------------------------------------------------------
-- The cut

checkCut :: Env -> Ctx -> ANode -> [Term] -> W ()
checkCut env cx an rest = do
  unexpected "the selected literal is the cut `!`, which has exactly one step, `!`" isCut an
  case [st | st <- aSteps an, isCut (stepKind (aS st))] of
    [] | null (aSteps an) -> err "E025" pos "the cut always succeeds: write the step `!` and the node below it"
       | otherwise        -> pure ()
    st : more -> do
      forM_ more $ \m -> err "E024" (stepPos (aS m)) "the cut has only one step"
      noSubst st
      descend env cx st [] M.empty rest True Nothing
  where
    pos = nodePos (aN an)
    isCut CutStep = True
    isCut _       = False

--------------------------------------------------------------------------------
-- Negation

checkNegation :: Env -> Ctx -> ANode -> Term -> [Term] -> W ()
checkNegation env cx an g rest = do
  unexpected ("the selected literal is `\\+ " ++ showT g ++ "`: its step is `\\+ @tree`") isNeg an
  case [st | st <- aSteps an, isNeg (stepKind (aS st))] of
    [] | null (aSteps an) -> err "E025" pos "write the step `\\+ @name` (naming the tree of the negated goal), or `\\+ @name fails`"
       | otherwise        -> pure ()
    st : more -> do
      forM_ more $ \m -> err "E024" (stepPos (aS m)) "a negation has only one step"
      one st
  where
    pos = nodePos (aN an)
    isNeg (Negation _)      = True
    isNeg (NegationFails _) = True
    isNeg _                 = False

    glits = goalLits g

    one st = do
      let (t, continues) = case stepKind (aS st) of
            Negation x      -> (x, True)
            NegationFails x -> (x, False)
            _               -> ("", True)
          spos = stepPos (aS st)
      noSubst st
      tell (Out [] [] [(t, spos)])
      -- the tree
      case M.lookup t (envTrees env) of
        Nothing
          | M.member t (envNames env) ->
              err "E040" spos ("@" ++ t ++ " is a node inside a tree; the tree of a negation is its own tree, starting at column 1")
          | otherwise ->
              err "E002" spos ("there is no tree @" ++ t ++ ": write the tree of the negated goal separately, with @" ++ t ++ " after its goal")
        Just inner -> do
          let ig = goalLits (toCore (nodeGoal (aN inner)))
          if ig /= glits
            then err "E040" (nodePos (aN inner)) ("the tree @" ++ t ++ " starts with " ++ qGoal ig ++ ", but the negated goal is " ++ qGoal glits)
            else pure ()
          walkTree env (cxUsed cx `S.union` S.fromList (termVars g)) inner False
          let provenNodes = [x | x <- preorder inner, null (goalLits (toCore (nodeGoal (aN x))))]
              drawnSuccess = not (null provenNodes)
          when continues $ forM_ (take 1 provenNodes) $ \x ->
            err "E042" spos ("this step says the negation succeeds, but the tree @" ++ t ++ " contains a proven node (line "
                             ++ show (posLine (nodePos (aN x))) ++ ")")
          when (not continues && not drawnSuccess) $
            err "E042" spos ("this step says the negation fails, but the tree @" ++ t ++ " contains no proven node")
      -- the outcome
      case refutes (envProg env) (goalFromLits glits) (envBudget env) of
        Nothing -> warn "W006" spos ("could not decide whether " ++ q g ++ " has a solution (step limit or unsupported built-in), so the outcome was not checked")
        Just refuted
          | continues && not refuted ->
              err "E041" spos (q g ++ " has a solution, so `\\+ " ++ showT g ++ "` fails: use `\\+ @" ++ t ++ " fails` and end the branch here")
          | not continues && refuted ->
              err "E041" spos (q g ++ " has no solution, so `\\+ " ++ showT g ++ "` succeeds: use `\\+ @" ++ t ++ "` and continue with the rest of the goal")
          | otherwise -> pure ()
      -- below the step
      if continues
        then do
          descend env cx st [] M.empty rest True Nothing
        else forM_ (aChild st) $ \c ->
          err "E024" (nodePos (aN c)) "the negation fails, so there is nothing below this step"

--------------------------------------------------------------------------------
-- Built-ins

checkBuiltin :: Env -> Ctx -> ANode -> Term -> BuiltinStep -> [Term] -> W ()
checkBuiltin env cx an sel b rest = case b of
  Succeeds -> do
    continuing "it succeeds without binding anything"
    forM_ (aSteps an) $ \st -> when (isBuiltin' (stepKind (aS st))) $
      forM_ (stepSubst (aS st)) $ \s -> unless (null [() | (v, t) <- s, toCore t /= Var v]) $
        err "E028" (stepPos (aS st)) (q sel ++ " binds nothing, but the substitution is " ++ showSub (toSub s))
  UnifyWith x y -> do
    continuing ("it unifies " ++ q x ++ " and " ++ q y)
  Failing why -> do
    when (null (aSteps an)) $
      err "E025" pos ("the built-in " ++ q sel ++ " fails (" ++ why ++ "): write `builtin fails` or `fails`")
    forM_ (aSteps an) $ \st -> case stepKind (aS st) of
      BuiltinFails -> pure ()
      Fails        -> pure ()
      k            -> err "E026" (stepPos (aS st)) ("the built-in " ++ q sel ++ " fails (" ++ why ++ "), so there is no derivation; the step " ++ describe k ++ " is wrong")
  Errors e ->
    warn "W003" pos ("the built-in " ++ q sel ++ " raises an error (" ++ e ++ "), which an SLD tree cannot show; this node was not checked further")
  Unsupported what ->
    warn "W001" pos (what ++ "; this node was not checked further")
  where
    pos = nodePos (aN an)
    isBuiltin' Builtin = True
    isBuiltin' _       = False

    -- the built-in succeeds: one step `builtin`
    continuing how = do
      forM_ (aSteps an) $ \st -> case stepKind (aS st) of
        Builtin -> pure ()
        k | k `elem` [BuiltinFails, Fails] ->
              err "E026" (stepPos (aS st)) ("the built-in " ++ q sel ++ " does not fail: " ++ how)
          | otherwise ->
              err "E024" (stepPos (aS st)) ("the step " ++ describe k ++ " does not fit: the selected literal is the built-in " ++ q sel ++ ", whose step is `builtin`")
      case [st | st <- aSteps an, isBuiltin' (stepKind (aS st))] of
        [] | null (aSteps an) -> err "E025" pos ("the built-in " ++ q sel ++ " succeeds (" ++ how ++ "): write the step `builtin` and the node below it")
           | otherwise        -> pure ()
        st : more -> do
          forM_ more $ \m -> err "E024" (stepPos (aS m)) "a built-in has only one step"
          let bs = fromMaybe [] (stepSubst (aS st))
          case b of
            UnifyWith x y -> do
              let (ds, valid) = unifierReport (stepPos (aS st)) x y bs
              tell (Out ds [] [])
              descend env cx st [] (toSub bs) rest valid (unifyHead x y)
            _ -> descend env cx st [] M.empty rest True Nothing

--------------------------------------------------------------------------------
-- Calls of the program's predicates

data Role = RResolve (Maybe Int) | RPruned Int | RMarker | RWrong

checkCall :: Env -> Ctx -> ANode -> Term -> [Term] -> W ()
checkCall env cx an sel rest = case predicateOf sel of
  Nothing -> err "E024" pos ("the selected literal " ++ q sel ++ " is not callable")
  Just pr -> call pr
  where
    n   = aN an
    pos = nodePos n
    depth = aDepth an

    call pr = do
      let clauses = M.findWithDefault [] pr (envDb env)
          rename  = renameVars (++ "#alt")
          alts    = [cl | cl <- clauses, isJust (unify sel (rename (clauseHead cl)))]
          altNos  = map clauseNo alts
          roles   = assign [] (aSteps an)
          pairs   = zip (aSteps an) roles
      when (null clauses) $
        warn "W002" pos ("the program has no clauses for " ++ pind pr ++ "; a real Prolog would raise an existence error, here it counts as `no rule`")
      -- wrong kinds of steps
      forM_ pairs $ \(st, r) -> case r of
        RWrong -> err "E024" (stepPos (aS st))
                    ("the step " ++ describe (stepKind (aS st)) ++ " does not fit here: the selected literal " ++ q sel
                     ++ " is a call of " ++ pind pr ++ ", whose steps are rules, `pruned` entries or `no rule`")
        _ -> pure ()
      -- failure markers
      let markers = [st | (st, RMarker) <- pairs]
          others  = [st | (st, r) <- pairs, isStepRole r]
      forM_ markers $ \st -> do
        unless (null alts) $
          err "E026" (stepPos (aS st))
            ("the branch does not fail here: " ++ clausesText pr alts ++ " unify with " ++ q sel)
        unless (null others) $
          err "E024" (stepPos (aS st)) "a failure marker cannot be combined with other steps"
      when (null (aSteps an) && null alts) $
        err "E025" pos ("no clause of " ++ pind pr ++ " unifies with " ++ q sel ++ ": write `no rule` (or `fails`) to end this branch")
      when (null (aSteps an) && not (null alts)) $
        err "E025" pos ("the branch ends without a reason, but " ++ clausesText pr alts ++ " unify with " ++ q sel ++ ": draw a rule step for each, or `pruned` entries")
      -- every alternative once, in order
      forM_ altNos $ \k -> do
        let hits = [st | (st, r) <- pairs, clauseOf r == Just k]
        when (null hits) $
          err "E022" pos ("clause " ++ show k ++ " of " ++ pind pr ++ " unifies with " ++ q sel
                          ++ " but is neither drawn nor pruned" ++ concat [": " ++ q (clauseTerm cl) | cl <- alts, clauseNo cl == k])
        forM_ (zip hits (drop 1 hits)) $ \(first, st) ->
          err "E023" (stepPos (aS st)) ("clause " ++ show k ++ " of " ++ pind pr ++ " is already used by the step at line " ++ show (posLine (stepPos (aS first))))
      checkOrder pr pairs
      -- the steps themselves
      forM_ (zip [0 :: Int ..] pairs) $ \(i, (st, r)) -> do
        let before = take i pairs
            earlierChildren = [c | (s', RResolve _) <- before, Just c <- [aChild s']]
            cutAbove = firstCutAbove depth earlierChildren
        case r of
          RResolve mk -> resolveStep pr st mk cutAbove
          RPruned k   -> prunedStep pr altNos st k cutAbove
          _           -> pure ()

    isStepRole (RResolve _) = True
    isStepRole (RPruned _)  = True
    isStepRole _            = False

    clauseOf (RResolve mk) = mk
    clauseOf (RPruned k)   = Just k
    clauseOf _             = Nothing

    clausesText pr alts = case map clauseNo alts of
      [k] -> "clause " ++ show k ++ " of " ++ pind pr
      ks  -> "clauses " ++ intercalate ", " (map show ks) ++ " of " ++ pind pr

    -- which clause does each step stand for?
    assign _ [] = []
    assign usedKs (st : sts) = case stepKind (aS st) of
      Resolve r ->
        let k = pickClause usedKs r
        in RResolve k : assign (maybe usedKs (: usedKs) k) sts
      Pruned _ k _ -> RPruned k : assign usedKs sts
      NoRule       -> RMarker : assign usedKs sts
      Fails        -> RMarker : assign usedKs sts
      _            -> RWrong : assign usedKs sts

    pickClause usedKs r = case predicateOf sel of
      Nothing -> Nothing
      Just pr ->
        let cands = [clauseNo cl | cl <- M.findWithDefault [] pr (envDb env), sameClause r cl]
        in listToMaybe ([k | k <- cands, k `notElem` usedKs] ++ cands)

    sameClause r cl = isVariant (asClause (toCore (freshenAnonymous r)))
                                (asClause (Compound ":-" [clauseHead cl, goalFromLits (clauseBody cl)]))
    asClause t = let (h, b) = splitClause t in Compound ":-" [h, goalFromLits b]

    checkOrder _ pairs = go 0 pairs
      where
        go _ [] = pure ()
        go lastK ((st, r) : more) = case clauseOf r of
          Just k | k < lastK -> do
                     err "E021" (stepPos (aS st)) ("clauses are tried in program order: clause " ++ show k ++ " comes before clause " ++ show lastK ++ ", but is written after it")
                     go lastK more
                 | otherwise -> go k more
          Nothing -> go lastK more

    -- a rule step
    resolveStep pr st mk cutAbove = case stepKind (aS st) of
     Resolve r0 -> resolveRule pr st mk cutAbove r0
     _          -> pure ()

    resolveRule pr st mk cutAbove r0 = do
      let spos = stepPos (aS st)
          r  = freshenAnonymous (toCore r0)
          (h, body) = splitClause r
      when (hasAnon r0) $ anonymous spos
      case cutAbove of
        Just c | isJust mk -> err "E033" spos
          ("clause " ++ show (fromJust mk) ++ " of " ++ pind pr ++ " is never tried: " ++ nodeRef c
           ++ " cuts it off. Write `pruned " ++ pind pr ++ " #" ++ show (fromJust mk) ++ " by @name` instead of a branch")
        _ -> do
          case predicateOf h of
            Just pr' | pr' /= pr ->
              err "E013" spos ("the rule is for " ++ pind pr' ++ ", but the selected literal " ++ q sel ++ " is a call of " ++ pind pr)
            Nothing -> err "E013" spos ("the rule head " ++ q h ++ " is not callable")
            _ -> do
              when (isNothing mk) $
                err "E011" spos ("the rule " ++ q r0 ++ " is not a renamed copy of any clause of " ++ pind pr
                                 ++ " (the program has: " ++ intercalate "  " (map (q . clauseTerm) (M.findWithDefault [] pr (envDb env))) ++ ")")
              let avoid = cxUsed cx `S.union` S.fromList (termVars (toCore (nodeGoal n)))
                  clash = [v | v <- termVars r, v `S.member` avoid, take 6 v /= "_anon#"]
              unless (null clash) $
                err "E012" spos ("the rule has not been renamed apart: " ++ intercalate ", " clash
                                 ++ (if length clash == 1 then " is" else " are")
                                 ++ " already used earlier in the derivation (root query, earlier rules or this goal); use fresh variables")
              let bs = fromMaybe [] (stepSubst (aS st))
                  (ds, valid) = unifierReport spos sel h bs
              tell (Out ds [] [])
              descend env cx st [r] (toSub bs) (body ++ rest) valid (unifyHead sel h)

    -- a pruned entry
    prunedStep pr altNos st k cutAbove = case stepKind (aS st) of
     Pruned pr' _ by -> prunedEntry pr altNos st k cutAbove pr' by
     _               -> pure ()

    prunedEntry pr altNos st k cutAbove pr' by = do
      let spos = stepPos (aS st)
      forM_ (aChild st) $ \_ -> err "E024" spos "a `pruned` entry has no node below it"
      noSubst st
      if pr' /= pr
        then err "E032" spos ("`pruned` names " ++ pind pr' ++ ", but the selected literal " ++ q sel ++ " is a call of " ++ pind pr)
        else if k `notElem` altNos
          then err "E032" spos
                 (if k `elem` [clauseNo cl | cl <- M.findWithDefault [] pr (envDb env)]
                    then "clause " ++ show k ++ " of " ++ pind pr ++ " is not an alternative here: its head does not unify with " ++ q sel
                    else pind pr ++ " has no clause " ++ show k)
          else do
            when (M.notMember by (envNames env)) $
              err "E002" spos ("there is no node @" ++ by ++ maybe "" (\c -> " (the cut that prunes this is " ++ nodeRef c ++ ")") cutAbove)
            case (cutAbove, M.lookup by (envNames env)) of
              (Nothing, _) -> err "E030" spos
                ("clause " ++ show k ++ " of " ++ pind pr ++ " is not pruned: no cut reaches this node from the branches before it. Draw its branch")
              (Just c, Just target)
                | nodePos (aN target) == nodePos (aN c) -> pure ()
                | isNothing (aCut target) ->
                    err "E031" spos ("@" ++ by ++ " is not a cut: its selected literal is not `!`. The cut that prunes this alternative is " ++ nodeRef c)
                | otherwise ->
                    err "E031" spos ("the cut @" ++ by ++ " does not prune this alternative; the first cut that does is " ++ nodeRef c)
              _ -> pure ()

--------------------------------------------------------------------------------
-- Answers

showAns :: [String] -> [Term] -> String
showAns qv tup =
  case [v ++ " = " ++ showT t | (v, t) <- zip qv (cleanVars tup), t /= Var v] of
    [] -> "true"
    bs -> intercalate ", " bs

-- | Variables made up by the solver get readable names.
cleanVars :: [Term] -> [Term]
cleanVars ts = map (renameVars (\v -> M.findWithDefault v v names)) ts
  where
    vs    = [v | v <- termVars (Compound "t" ts), '#' `elem` v]
    names = M.fromList (zip vs ["_G" ++ show i | i <- [1 :: Int ..]])

-- | Match answers up to renaming; returns (unmatched in the first list,
--   unmatched in the second).
pairUp :: [[Term]] -> [[Term]] -> ([[Term]], [[Term]])
pairUp xs0 ys0 = go xs0 ys0 []
  where
    same x y = isVariant (Compound "ans" x) (Compound "ans" y)
    go [] ys acc       = (reverse acc, ys)
    go (x : xs) ys acc = case break (same x) ys of
      (pre, _ : post) -> go xs (pre ++ post) acc
      (_, [])         -> go xs ys (x : acc)
