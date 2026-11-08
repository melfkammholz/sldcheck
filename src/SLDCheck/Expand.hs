-- | References between trees.  Below a step, @\@t@ can stand for a node:
-- the root of the tree @t@, written separately.  This keeps deep trees
-- readable.  The checker works on the tree with the references replaced by
-- the trees they name, so cut, answers and renaming behave as if the tree
-- had been written in one piece; diagnostics still point to the place where
-- each part was written.
--
-- A tree used like this is part of the tree that refers to it.  It is not
-- the tree of a negation (that is @\\+ \@t@), and it can be used only once.
module SLDCheck.Expand (expandForest) where

import Control.Monad.Writer.Strict
import Data.List (nub)
import qualified Data.Map.Strict as M

import SLDCheck.Diagnostic
import SLDCheck.Tree

-- | The forest with every reference replaced.  The trees that were used as
--   parts of others no longer appear as trees of their own.
expandForest :: Forest -> (Forest, [Diagnostic])
expandForest [] = ([], [])
expandForest forest@(root : others) = (expanded, nub (refProblems ++ ds))
  where
    table    = M.fromList [(n, r) | r <- others, Just n <- [nodeName r]]
    mainName = nodeName root

    steps    = [s | r <- forest, nd <- nodesOf r, s <- nodeSteps nd]
    refs     = [(n, p) | Step { stepRef = Just (n, p) } <- steps]
    refNames = nub (map fst refs)
    negs     = [(n, stepPos s) | s <- steps, Just n <- [negName (stepKind s)]]

    negName (Negation n)      = Just n
    negName (NegationFails n) = Just n
    negName _                 = Nothing

    refProblems =
      [ diagnostic Error "E005" p ("the tree @" ++ n ++ " is already used as part of a tree at line " ++ show (posLine first)
                                   ++ "; a tree can be a part of one step only")
      | n <- refNames, (first : more) <- [[p' | (n', p') <- refs, n' == n]], p <- more ]
      ++
      [ diagnostic Error "E008" p ("the tree @" ++ n ++ " is used as a part of a tree and as the tree of a negation")
      | (n, p) <- negs, n `elem` refNames ]

    (expanded, ds) = runWriter $ do
      r  <- expandNode [maybe "" id mainName] root
      rs <- sequence [ expandNode [maybe "" id (nodeName o)] o
                     | o <- others, maybe True (`notElem` refNames) (nodeName o) ]
      pure (r : rs)

    expandNode :: [String] -> Node -> Writer [Diagnostic] Node
    expandNode vis n = do
      steps' <- mapM (expandStep vis) (nodeSteps n)
      pure n { nodeSteps = steps' }

    expandStep :: [String] -> Step -> Writer [Diagnostic] Step
    expandStep vis s = case stepRef s of
      Nothing -> do
        child <- traverse (expandNode vis) (stepChild s)
        pure s { stepChild = child }
      Just (name, p)
        | name `elem` vis || Just name == mainName -> do
            tell [diagnostic Error "E007" p ("the tree @" ++ name ++ " contains itself: it is reached again through this reference")]
            pure s
        | Just r <- M.lookup name table -> do
            r' <- expandNode (name : vis) r
            pure s { stepChild = Just r', stepRef = Nothing }
        | otherwise -> do
            tell [diagnostic Error "E002" p ("there is no tree @" ++ name ++ ": write it separately, with @" ++ name ++ " after its goal")]
            pure s
