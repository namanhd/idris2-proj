module NatExpr
import Data.So
import Data.Nat

-- (Expr n) is the type of all expression trees that eventually evaluate to n
-- (in this spirit you could also have a type of typed abstract syntax trees
-- using some sumtype representing "types", i.e. (Expr t) is the type of all
-- expression trees that are well-typed and have type t. 
data Expr : Nat -> Type where
  N : (n : Nat) -> Expr n
  -- {m: Nat} and {n: Nat} make sure that these are available at runtime (in
  -- Idris 1 these would not be needed, but in Idris 2, by default, if we left
  -- them out, m and n would be multiplicity 0, and thus "not accessible" at
  -- runtime, which means not accessible in pattern matching etc). This is a
  -- nice new feature; type-level values might not be needed at runtime and only
  -- at compile time (unless we specify we need it) which makes runtime a bit
  -- lighter.
  Add : {m: Nat} -> {n: Nat} -> Expr m -> Expr n -> Expr (m + n)
  Mult : {m: Nat} -> {n: Nat} -> Expr m -> Expr n -> Expr (m * n)      


-- cool interface for types dependent on a Nat, and which you can do Nat-like
-- operations on. (We could define an analogous DepNum interface that is this
-- but for any type with a Num instance, too, though Nats are easier to prove
-- things with.)
interface DepNat (motive : Nat -> Type) where
  (:+) : {a: Nat} -> {b: Nat} -> motive a -> motive b -> motive (a + b)
  (:*) : {a: Nat} -> {b: Nat} -> motive a -> motive b -> motive (a * b)
  dfromNat : (a: Nat) -> motive a

infixl 3 :+
infixl 4 :*

DepNat Expr where
  (:+) = Add
  (:*) = Mult
  dfromNat = N


-- single-step simplifier; a fully recursive simplifier wouldn't be obviously
-- totality-checkable, this is a bit nicer
-- (the "with" block instead of "case" block also helps the totality checker) 
total
step : {k: Nat} -> (Expr k) -> Maybe (Expr k)
step (N k) = Nothing
step (Add {m} {n} a b) with (step a)
  _ | Just a' = Just $ Add a' b
  _ | Nothing with (step b)
    _ | Just b' = Just $ Add a b'
    _ | Nothing = Just $ N (m + n)
step (Mult {m} {n} a b) with (step a)
  _ | Just a' = Just $ Mult a' b
  _ | Nothing with (step b)
    _ | Just b' = Just $ Mult a b'
    _ | Nothing = Just $ N (m * n)



total
eval : {k: Nat} -> Expr k -> Nat
eval {k} _ = k   -- we don't even need to recurse `step`, we just look at the type


-- actual simplification-steps function
total
simplify : {k: Nat} -> Expr k -> List (Expr k)
simplify e with (step e)
  _ | Just e' = e' :: simplify (assert_smaller e e')
  _ | Nothing = [] 

-- proofs..
total
eval_is_distrib : {0 a: Expr na} -> {0 b: Expr nb} -> (eval a + eval b = n) -> (eval (a :+ b) = n)
eval_is_distrib = id   -- LOL wtf   this is too cheesy 

total 
eval_is_distrib2 : (eval a + eval b = eval (a :+ b))
eval_is_distrib2 = Refl   -- ...yeah 

total
-- we need these implicit args to tell the type checker that na is different
-- from nb (otherwise it'll assume a and b are both Expr k for the same and only
-- 'k')
eval_plus_commutes : {na : Nat} -> {nb : Nat} -> {a: Expr na} -> {b: Expr nb} 
  -> (eval a + eval b = eval b + eval a)
eval_plus_commutes = plusCommutative (eval a) (eval b)
