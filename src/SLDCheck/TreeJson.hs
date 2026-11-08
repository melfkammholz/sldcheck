-- | The tree as JSON, for tools that draw it: @sldcheck --tree@.
--
-- > { "version": "0.3.0.0",
-- >   "tree":      Node | null,       -- the query's tree, references replaced by the trees they name
-- >   "negations": [Node],            -- the other trees, each with its "name"
-- >   "diagnostics": [...] }          -- syntax errors (then there is no tree) and the problems with references
--
-- A node and a step are
--
-- > Node = { "line", "column", "goal": "member(X, [1, 2]), Y is X + 1", "name": "c" | null,
-- >          "answer": [{"var": "X", "term": "1"}] | null, "steps": [Step] }
-- > Step = { "line", "column", "kind", "child": Node | null, ... }
--
-- The kinds, and what else a step has:
--
-- > "resolve"          "rule": "member(X2, [_2|T2]) :- member(X2, T2)", "subst": [Binding] | null
-- > "builtin"          "subst": [Binding] | null
-- > "cut"
-- > "negation"         "tree": "t1"            -- the name of the tree of the negated goal
-- > "negation-fails"   "tree": "t1"
-- > "pruned"           "predicate": "member/2", "clause": 2, "by": "c"
-- > "no-rule"  "builtin-fails"  "fails"
--
-- A step that refers to a tree that does not exist has @"ref": "name"@ and no child.
-- Terms are printed as Prolog, with the variables as they were written.
module SLDCheck.TreeJson
  ( renderTree
  ) where

import SLDCheck.Diagnostic
import SLDCheck.Json
import SLDCheck.Prolog
import SLDCheck.Tree
import SLDCheck.Version (version)

-- | The JSON text for a forest that has been through "SLDCheck.Expand".
renderTree :: Files -> OpTable -> Maybe Forest -> [Diagnostic] -> String
renderTree fs ops forest ds = render (Obj
  [ ("version", Str version)
  , ("tree", maybe Null (node ops) (mainTree forest))
  , ("negations", Arr (map (node ops) (others forest)))
  , ("diagnostics", diagnosticsValue fs ds) ]) ++ "\n"
  where
    mainTree (Just (t : _)) = Just t
    mainTree _              = Nothing
    others (Just (_ : ts))  = ts
    others _                = []

node :: OpTable -> Node -> Value
node ops n = Obj
  [ ("line", Num (posLine (nodePos n)))
  , ("column", Num (posCol (nodePos n)))
  , ("goal", Str (showTermWith ops (nodeGoal n)))
  , ("name", maybe Null Str (nodeName n))
  , ("answer", maybe Null (bindings ops) (nodeAnswer n))
  , ("steps", Arr (map (step ops) (nodeSteps n))) ]

bindings :: OpTable -> Subst -> Value
bindings ops s = Arr [Obj [("var", Str v), ("term", Str (showTermWith ops t))] | (v, t) <- s]

step :: OpTable -> Step -> Value
step ops s = Obj $
  [ ("line", Num (posLine (stepPos s)))
  , ("column", Num (posCol (stepPos s)))
  , ("kind", Str kind) ]
  ++ extra
  ++ [("subst", bindings ops sub) | Just sub <- [stepSubst s], hasSubst]
  ++ [("ref", Str r) | Just (r, _) <- [stepRef s]]
  ++ [("child", maybe Null (node ops) (stepChild s))]
  where
    hasSubst = case stepKind s of
      Resolve _ -> True
      Builtin   -> True
      _         -> False
    (kind, extra) = case stepKind s of
      Resolve r            -> ("resolve", [("rule", Str (showTermWith ops r))])
      Builtin              -> ("builtin", [])
      CutStep              -> ("cut", [])
      Negation t           -> ("negation", [("tree", Str t)])
      NegationFails t      -> ("negation-fails", [("tree", Str t)])
      Pruned (p, n) k by   -> ("pruned", [("predicate", Str (p ++ "/" ++ show n)), ("clause", Num k), ("by", Str by)])
      NoRule               -> ("no-rule", [])
      BuiltinFails         -> ("builtin-fails", [])
      Fails                -> ("fails", [])
