-- | A reference Prolog solver for the checker: depth-first search with the
--   leftmost selection rule and the clauses in program order, with the cut
--   (@!@) and negation as failure (@\\+@).  It never looks at a tree; the
--   checker uses it to know the true answers of a query and whether a negated
--   goal succeeds.
--
-- The solver is a small abstract machine: the goals still to prove (each
-- literal remembers how many choice points existed when its clause was
-- entered, which is what a cut removes) and a stack of choice points.
module SLDCheck.Solve
  ( Result(..)
  , solveQuery
  , refutes
  ) where

import Control.Monad (forM)
import Control.Monad.State.Strict
import qualified Data.Map.Strict as M

import SLDCheck.Logic
import SLDCheck.Prolog

-- | The answers of a query, in the order Prolog finds them.
data Result = Result
  { resAnswers  :: [[Term]]   -- ^ the values of the query's variables (in order of first occurrence)
  , resComplete :: Bool       -- ^ False if the search ran out of steps or met something it cannot do
  }

-- | A literal and the height of the choice point stack a cut in it returns to.
data G = G Term Int

data S = S { fuel :: !Int, fresh :: !Int, partial :: !Bool }

-- | @solveQuery program query budget@; the budget bounds the number of steps.
solveQuery :: Program -> Term -> Int -> Result
solveQuery prog query budget = Result [[a M.! v | v <- qvars] | a <- answers] (not (partial st))
  where
    qc    = toCore query
    qvars = termVars qc
    (answers, st) = runState
      (search (indexProgram prog) maxBound [G l 0 | l <- goalLits qc]
              (M.fromList [(v, Var v) | v <- qvars]))
      (S budget 0 False)

-- | Does the goal have no solution?  Nothing if that could not be decided.
refutes :: Program -> Term -> Int -> Maybe Bool
refutes prog goal budget
  | not (null answers) = Just False
  | partial st         = Nothing
  | otherwise          = Just True
  where
    (answers, st) = runState (search (indexProgram prog) 1 [G l 0 | l <- goalLits (toCore goal)] M.empty)
                             (S budget 0 False)

type Frame = ([G], Sub)

-- | At most @limit@ answers; each is the final binding of the query variables.
search :: M.Map Indicator [Clause] -> Int -> [G] -> Sub -> State S [Sub]
search db limit goals0 ans0 = loop goals0 ans0 [] []
  where
    loop :: [G] -> Sub -> [Frame] -> [Sub] -> State S [Sub]
    loop goals ans cps acc
      | length acc >= limit = pure (reverse acc)
      | otherwise = do
          s <- get
          if fuel s <= 0
            then put s { partial = True } >> pure (reverse acc)
            else do
              put s { fuel = fuel s - 1 }
              case goals of
                []            -> backtrack cps (ans : acc)
                G lit b : rest -> select lit b rest ans cps acc

    backtrack [] acc               = pure (reverse acc)
    backtrack ((gs, a) : cps) acc  = loop gs a cps acc

    giveUp cps acc = modify' (\s -> s { partial = True }) >> backtrack cps acc

    select lit b rest ans cps acc = case lit of
      Atom "!" -> loop rest ans (drop (length cps - b) cps) acc
      Compound "\\+" [g] -> do
        inner <- search db 1 [G l 0 | l <- goalLits g] M.empty
        if null inner then loop rest ans cps acc else backtrack cps acc
      _ -> case builtinStep lit of
        Just Succeeds        -> loop rest ans cps acc
        Just (UnifyWith x y) -> case unify x y of
          Nothing    -> backtrack cps acc
          Just theta -> loop (applyG theta rest) (M.map (applySub theta) ans) cps acc
        Just (Failing _)       -> backtrack cps acc
        Just (Errors _)      -> giveUp cps acc
        Just (Unsupported _) -> giveUp cps acc
        Nothing -> do
          let h = length cps
          alts <- forM (maybe [] id (predicateOf lit >>= (`M.lookup` db))) $ \cl -> do
            k <- gets fresh
            modify' (\s -> s { fresh = k + 1 })
            let ren = renameVars (++ "#" ++ show k)
            pure $ case unify lit (ren (clauseHead cl)) of
              Nothing    -> Nothing
              Just theta -> Just ( [G (applySub theta (ren l)) h | l <- clauseBody cl] ++ applyG theta rest
                                 , M.map (applySub theta) ans )
          case [a | Just a <- alts] of
            []            -> backtrack cps acc
            (gs, a) : more -> loop gs a (more ++ cps) acc

    applyG theta = map (\(G l b) -> G (applySub theta l) b)
