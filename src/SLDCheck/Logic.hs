-- | The logic needed to check SLD derivations: substitutions, unification,
--   variants and arithmetic built-ins.
--
-- Internally lists are turned into cons cells (@'[|]'(H, T)@) so that
-- @[a,b]@, @[a|[b]]@ and @'[|]'(a, '[|]'(b, []))@ are the same term; use
-- 'showT' to print a term in normal Prolog syntax again.
module SLDCheck.Logic
  ( Sub
  , Program
    -- * Terms
  , toCore, fromCore, showT, showSub
  , termVars, renameVars, applySub, freshenAnonymous
  , goalLits, goalFromLits, splitClause, predicateOf, callable
    -- * Programs
  , Clause(..), Indicator, indexProgram
    -- * Unification
  , unify, unifyPreferring, isVariant
    -- * Built-ins
  , BuiltinStep(..), builtinStep, isBuiltin
  ) where

import Control.Monad
import Data.Bits (complement, shiftL, shiftR, xor, (.&.), (.|.))
import Data.List (intercalate, isPrefixOf, mapAccumL, nub)
import qualified Data.Map.Strict as M

import SLDCheck.Prolog

-- | A substitution, applied simultaneously.
type Sub = M.Map String Term

-- | A list of clauses (facts and @:-@ rules).
type Program = [Term]

--------------------------------------------------------------------------------
-- Terms

-- | Lists become cons cells, so that equal lists are equal terms.
toCore :: Term -> Term
toCore t = case t of
  List xs tl    -> foldr (\h r -> Compound "[|]" [h, r]) (maybe (Atom "[]") toCore tl) (map toCore xs)
  Compound f as -> Compound f (map toCore as)
  _             -> t

-- | The inverse of 'toCore', for printing.
fromCore :: Term -> Term
fromCore t = case t of
  Compound "[|]" [h, r] -> collect [fromCore h] r
  Compound f as         -> Compound f (map fromCore as)
  _                     -> t
  where
    collect acc (Compound "[|]" [h', r']) = collect (fromCore h' : acc) r'
    collect acc (Atom "[]")               = List (reverse acc) Nothing
    collect acc tl                        = List (reverse acc) (Just (fromCore tl))

-- | A term in Prolog syntax (works on core and ordinary terms).  Variables
--   made by 'freshenAnonymous' are shown as @_@ again.
showT :: Term -> String
showT = show . fromCore . renameVars hide
  where hide v | "_anon#" `isPrefixOf` v = "_"
               | otherwise               = v

-- | Make every anonymous variable @_@ a variable of its own, as in Prolog
--   (@p(_, _)@ has two different variables).  Used for the clauses of a
--   program; the names contain @#@, so they cannot clash with source names.
freshenAnonymous :: Term -> Term
freshenAnonymous = snd . go (0 :: Int)
  where
    go n (Var "_")       = (n + 1, Var ("_anon#" ++ show n))
    go n (Compound f as) = Compound f <$> mapAccumL go n as
    go n (List xs tl)    =
      let (n1, xs') = mapAccumL go n xs
      in case tl of
           Nothing -> (n1, List xs' Nothing)
           Just x  -> let (n2, x') = go n1 x in (n2, List xs' (Just x'))
    go n t               = (n, t)

showSub :: Sub -> String
showSub s = "{" ++ intercalate ", " [v ++ " |-> " ++ showT t | (v, t) <- M.toList s] ++ "}"

-- | Variables in order of first occurrence.
termVars :: Term -> [String]
termVars = nub . go
  where
    go (Var v)        = [v]
    go (Compound _ as) = concatMap go as
    go (List xs tl)   = concatMap go xs ++ maybe [] go tl
    go _              = []

renameVars :: (String -> String) -> Term -> Term
renameVars f = go
  where
    go (Var v)         = Var (f v)
    go (Compound g as) = Compound g (map go as)
    go (List xs tl)    = List (map go xs) (fmap go tl)
    go t               = t

applySub :: Sub -> Term -> Term
applySub s = go
  where
    go t@(Var v)       = M.findWithDefault t v s
    go (Compound f as) = Compound f (map go as)
    go (List xs tl)    = List (map go xs) (fmap go tl)
    go t               = t

-- | The literals of a goal (a conjunction).  The goal @true@ is the empty goal.
goalLits :: Term -> [Term]
goalLits (Atom "true") = []
goalLits t             = flatten t

flatten :: Term -> [Term]
flatten (Compound "," [a, b]) = flatten a ++ flatten b
flatten t                     = [t]

-- | Build a goal; the empty goal is @true@.
goalFromLits :: [Term] -> Term
goalFromLits []  = Atom "true"
goalFromLits ls  = foldr1 (\a b -> Compound "," [a, b]) ls

-- | Head and body literals of a clause (a fact has an empty body).
splitClause :: Term -> (Term, [Term])
splitClause (Compound ":-" [h, b]) = (h, flatten b)
splitClause h                      = (h, [])

-- | Name and arity of an atom or compound term.
predicateOf :: Term -> Maybe (String, Int)
predicateOf (Atom a)                   = Just (a, 0)
predicateOf (Compound f as) | f /= "[|]" = Just (f, length as)
predicateOf _                          = Nothing

callable :: Term -> Bool
callable = (/= Nothing) . predicateOf

--------------------------------------------------------------------------------
-- Programs

-- | Name and arity.
type Indicator = (String, Int)

-- | A clause of the program, numbered within its predicate (the first clause
--   of @p/2@ is number 1, whatever comes before it in the file).
data Clause = Clause
  { clauseNo   :: Int            -- ^ position among the clauses of its predicate
  , clauseTerm :: Term           -- ^ as written (lists as 'List', @_@ as @_@)
  , clauseHead :: Term           -- ^ core form, every @_@ a variable of its own
  , clauseBody :: [Term]         -- ^ the same
  }

-- | The clauses by predicate, in program order.  Directives (@:- ...@) and
--   terms that are not callable are skipped.
indexProgram :: Program -> M.Map Indicator [Clause]
indexProgram prog = M.map (zipWith number [1 ..] . reverse) $
  M.fromListWith (++) [ (pi', [(t, h, b)]) | t <- prog, notDirective t
                      , let (h, b) = splitClause (freshenAnonymous (toCore t))
                      , Just pi' <- [predicateOf h] ]
  where
    number k (t, h, b) = Clause k t h b
    notDirective (Compound ":-" [_]) = False
    notDirective (Compound "?-" [_]) = False
    notDirective _                   = True

--------------------------------------------------------------------------------
-- Unification

-- | A most general unifier (with occurs check), fully resolved, or Nothing.
unify :: Term -> Term -> Maybe Sub
unify = unifyPreferring (const False)

-- | Like 'unify'.  When two variables meet, the one satisfying the predicate
--   is the one that gets bound (so the variables of a renamed rule are bound
--   to those of the goal, not the other way round).
unifyPreferring :: (String -> Bool) -> Term -> Term -> Maybe Sub
unifyPreferring prefer a b = resolveTri <$> go M.empty (toCore a) (toCore b)
  where
    go s x y = case (walk s x, walk s y) of
      (Var v, Var w) | v == w -> Just s
                     | prefer w && not (prefer v) -> bind w (Var v) s
      (Var v, t)              -> bind v t s
      (t, Var v)              -> bind v t s
      (Compound f as, Compound g bs)
        | f == g && length as == length bs ->
            foldM (\s' (p, q) -> go s' p q) s (zip as bs)
        | otherwise -> Nothing
      (x', y') | x' == y'  -> Just s
               | otherwise -> Nothing

    walk s (Var v) | Just t <- M.lookup v s = walk s t
    walk _ t = t

    bind v t s
      | occurs s v t = Nothing
      | otherwise    = Just (M.insert v t s)

    occurs s v t = case walk s t of
      Var w         -> v == w
      Compound _ as -> any (occurs s v) as
      _             -> False

-- | Resolve a triangular substitution (see 'unify').
resolveTri :: Sub -> Sub
resolveTri s = M.map (deepApply s) s

deepApply :: Sub -> Term -> Term
deepApply s t = case t of
  Var v         -> maybe t (deepApply s) (M.lookup v s)
  Compound f as -> Compound f (map (deepApply s) as)
  _             -> t

-- | Are the terms equal up to a renaming of variables?
isVariant :: Term -> Term -> Bool
isVariant a b = maybe False (const True) (go (M.empty, M.empty) (toCore a) (toCore b))
  where
    go m@(fw, bw) x y = case (x, y) of
      (Var v, Var w) -> case (M.lookup v fw, M.lookup w bw) of
        (Nothing, Nothing)           -> Just (M.insert v w fw, M.insert w v bw)
        (Just w', Just v') | w' == w && v' == v -> Just m
        _                            -> Nothing
      (Compound f as, Compound g bs)
        | f == g && length as == length bs ->
            foldM (\m' (p, q) -> go m' p q) m (zip as bs)
        | otherwise -> Nothing
      (Var _, _) -> Nothing
      (_, Var _) -> Nothing
      _ | x == y    -> Just m
        | otherwise -> Nothing

--------------------------------------------------------------------------------
-- Arithmetic and built-ins

data N = NI Integer | NF Double

toD :: N -> Double
toD (NI n) = fromInteger n
toD (NF x) = x

numTerm :: N -> Term
numTerm (NI n) = IntLit n
numTerm (NF x) = FloatLit x

cmpN :: N -> N -> Ordering
cmpN (NI a) (NI b) = compare a b
cmpN a b           = compare (toD a) (toD b)

-- | Evaluate an arithmetic expression.
eval :: Term -> Either String N
eval t = case t of
  IntLit n          -> Right (NI n)
  FloatLit x        -> Right (NF x)
  Var v             -> Left ("instantiation error: " ++ v ++ " is not bound")
  Atom "pi"         -> Right (NF pi)
  Atom "e"          -> Right (NF (exp 1))
  Compound f [a]    -> eval a >>= unary f
  Compound f [a, b] -> do { x <- eval a; y <- eval b; binary f x y }
  _                 -> Left ("type error: " ++ showT t ++ " is not an arithmetic expression")

unary :: String -> N -> Either String N
unary f x = case (f, x) of
  ("-", NI n)  -> Right (NI (negate n))
  ("-", NF d)  -> Right (NF (negate d))
  ("+", _)     -> Right x
  ("abs", NI n) -> Right (NI (abs n))
  ("abs", NF d) -> Right (NF (abs d))
  ("sign", NI n) -> Right (NI (signum n))
  ("sign", NF d) -> Right (NF (signum d))
  ("sqrt", _) | toD x < 0 -> Left "evaluation error: undefined (sqrt of a negative number)"
              | otherwise -> Right (NF (sqrt (toD x)))
  ("float", _)   -> Right (NF (toD x))
  ("truncate", _) -> Right (NI (truncate (toD x)))
  ("floor", _)    -> Right (NI (floor (toD x)))
  ("ceiling", _)  -> Right (NI (ceiling (toD x)))
  ("round", _)    -> Right (NI (round (toD x)))
  ("\\", NI n)    -> Right (NI (complement n))
  _ -> Left ("type error: " ++ f ++ "/1 is not an evaluable function (or needs an integer)")

binary :: String -> N -> N -> Either String N
binary f x y = case (f, x, y) of
  ("+", NI a, NI b) -> Right (NI (a + b))
  ("+", _, _)       -> Right (NF (toD x + toD y))
  ("-", NI a, NI b) -> Right (NI (a - b))
  ("-", _, _)       -> Right (NF (toD x - toD y))
  ("*", NI a, NI b) -> Right (NI (a * b))
  ("*", _, _)       -> Right (NF (toD x * toD y))
  ("/", NI a, NI b)
    | b == 0          -> zeroDiv
    | a `mod` b == 0  -> Right (NI (a `div` b))
    | otherwise       -> Right (NF (fromInteger a / fromInteger b))
  ("/", _, _)
    | toD y == 0 -> zeroDiv
    | otherwise  -> Right (NF (toD x / toD y))
  ("//",  NI a, NI b) | b == 0 -> zeroDiv | otherwise -> Right (NI (a `quot` b))
  ("div", NI a, NI b) | b == 0 -> zeroDiv | otherwise -> Right (NI (a `div` b))
  ("mod", NI a, NI b) | b == 0 -> zeroDiv | otherwise -> Right (NI (a `mod` b))
  ("rem", NI a, NI b) | b == 0 -> zeroDiv | otherwise -> Right (NI (a `rem` b))
  ("min", _, _) -> Right (if cmpN x y == GT then y else x)
  ("max", _, _) -> Right (if cmpN x y == LT then y else x)
  ("^", NI a, NI b)
    | b >= 0    -> Right (NI (a ^ b))
    | a == 1    -> Right (NI 1)
    | a == -1   -> Right (NI (if even b then 1 else -1))
    | otherwise -> Left "type error: integer ^ negative integer is not an integer"
  ("**", NI a, NI b) | b >= 0 -> Right (NI (a ^ b))
  ("^",  _, _) -> Right (NF (toD x ** toD y))
  ("**", _, _) -> Right (NF (toD x ** toD y))
  ("<<",  NI a, NI b) -> Right (NI (a `shiftL` fromInteger b))
  (">>",  NI a, NI b) -> Right (NI (a `shiftR` fromInteger b))
  ("/\\", NI a, NI b) -> Right (NI (a .&. b))
  ("\\/", NI a, NI b) -> Right (NI (a .|. b))
  ("xor", NI a, NI b) -> Right (NI (a `xor` b))
  _ -> Left ("type error: " ++ f ++ "/2 is not an evaluable function (or needs integers)")
  where zeroDiv = Left "evaluation error: zero_divisor"

-- | What a built-in predicate does as the selected literal.
data BuiltinStep
  = Succeeds                  -- ^ succeeds without binding anything
  | UnifyWith Term Term       -- ^ succeeds iff the two terms unify (and then binds like the mgu)
  | Failing String              -- ^ fails (with the reason)
  | Errors String             -- ^ raises an error
  | Unsupported String        -- ^ outside pure SLD resolution; cannot be checked

-- | The behaviour of a built-in, or Nothing for an ordinary predicate.
--   Supported: true, fail/false, =, \\=, ==, \\==, is, the arithmetic
--   comparisons.  The cut and the control constructs (;, ->, \\+, call, ...)
--   are recognised but 'Unsupported'.
builtinStep :: Term -> Maybe BuiltinStep
builtinStep t = case t of
  Atom "true"             -> Just Succeeds
  Atom "fail"             -> Just (Failing "fail")
  Atom "false"            -> Just (Failing "false")
  Atom "!"                -> Just (Unsupported "the cut (!) is not part of pure SLD resolution")
  Compound "=" [a, b]     -> Just (UnifyWith a b)
  Compound "\\=" [a, b]   -> Just (maybe Succeeds (const (Failing "the terms unify")) (unify a b))
  Compound "==" [a, b]
    | toCore a == toCore b -> Just Succeeds
    | otherwise            -> Just (Failing "the terms are not identical")
  Compound "\\==" [a, b]
    | toCore a /= toCore b -> Just Succeeds
    | otherwise            -> Just (Failing "the terms are identical")
  Compound "is" [l, e]    -> Just (either Errors (UnifyWith l . numTerm) (eval e))
  Compound op [a, b]
    | Just test <- lookup op comparisons ->
        Just $ case (eval a, eval b) of
          (Left e, _)  -> Errors e
          (_, Left e)  -> Errors e
          (Right x, Right y)
            | test (cmpN x y) -> Succeeds
            | otherwise       -> Failing (showT t ++ " is false")
  Compound c _ | c `elem` controls -> Just (control c)
  Atom c       | c `elem` controls -> Just (control c)
  _ -> Nothing
  where
    comparisons =
      [ ("<", (== LT)), (">", (== GT)), ("=<", (/= GT)), (">=", (/= LT))
      , ("=:=", (== EQ)), ("=\\=", (/= EQ)) ]
    controls = [";", "->", "*->", "\\+", "call", "findall", "forall", "bagof", "setof", "catch"]
    control c = Unsupported ("the control construct " ++ c ++ " is not part of pure SLD resolution")

isBuiltin :: Term -> Bool
isBuiltin t = case builtinStep t of
  Nothing -> False
  Just _  -> True
