-- | The abstract syntax of an SLD tree as a student writes it (see
--   NOTATION.md).  Nothing here is checked: the types only record what was
--   written, together with where it was written.
module SLDCheck.Tree
  ( Pos(..)
  , Subst
  , Node(..)
  , Step(..)
  , StepKind(..)
  , Forest
  , nodesOf
  ) where

import SLDCheck.Prolog (Term)

-- | A line and a column, both starting at 1.
data Pos = Pos { posLine :: !Int, posCol :: !Int }
  deriving (Eq, Ord, Show)

-- | @Var |-> Term@ bindings, in source order.
type Subst = [(String, Term)]

-- | A goal ("query") together with the derivation steps that start from it.
data Node = Node
  { nodePos    :: Pos
  , nodeName   :: Maybe String   -- ^ @\@c@, how other parts of the file refer to it
  , nodeGoal   :: Term           -- ^ the goal; @true@ is the empty goal
  , nodeAnswer :: Maybe Subst    -- ^ the answer substitution written after the goal
  , nodeSteps  :: [Step]         -- ^ in the order they were written
  } deriving (Eq, Show)

-- | One entry below a node: a derivation to a child, or a statement about why
--   there is none.
data Step = Step
  { stepPos   :: Pos
  , stepKind  :: StepKind
  , stepSubst :: Maybe Subst     -- ^ the @{...}@ line, if there was one
  , stepChild :: Maybe Node
  , stepRef   :: Maybe (String, Pos)
    -- ^ @\@t@ instead of a node: the child is the root of the tree @t@
    --   written elsewhere (see "SLDCheck.Expand", which replaces it by the node)
  , stepClause :: Maybe Int
    -- ^ for a rule step: the number of the clause (within its predicate, from 1)
    --   the rule is a renamed copy of.  The parser leaves it empty;
    --   'SLDCheck.Check.numberRules' fills it in when the program is known.
  } deriving (Eq, Show)

data StepKind
  = Resolve Term                 -- ^ resolution with this renamed clause
  | Builtin                      -- ^ a built-in was evaluated
  | CutStep                      -- ^ @!@ was selected
  | Negation String              -- ^ @\\+ \@t@: the negated goal is refuted by the tree @t@
  | Pruned (String, Int) Int String
    -- ^ @pruned p/n #k by \@c@: predicate, clause number, the cut node
  | NoRule                       -- ^ @no rule@
  | BuiltinFails                 -- ^ @builtin fails@
  | NegationFails String         -- ^ @\\+ \@t fails@
  | Fails                        -- ^ @fails@: a failure without a stated reason
  deriving (Eq, Show)

-- | The trees of a file.  The first is the query, the others are the trees of
--   negated goals.
type Forest = [Node]

-- | A node and all nodes below it, in the order they are written.
nodesOf :: Node -> [Node]
nodesOf n = n : concat [nodesOf c | Step { stepChild = Just c } <- nodeSteps n]
