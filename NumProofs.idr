module NumProofs
import Data.So
import Data.Nat

Pint : Type
Pint = (Nat, Nat)

total
normalize' : Nat -> Nat -> Pint
normalize' (S a) (S b) = normalize' a b
normalize' Z a = (Z, a)
normalize' a Z = (a, Z)

total
normalize : Pint -> Pint
normalize (a, b) = normalize' a b

total
pintNegate : Pint -> Pint
pintNegate (a, b) = (b, a)

total
pintToInt : Pint -> Integer
pintToInt (a, b) = natToInteger a - natToInteger b

total
intToPint : Integer -> Pint
intToPint n = if n >= 0 then (integerToNat n, Z) else (Z, integerToNat $ -n)

total
intToPint' : (n: Integer) -> Either (So (n >= 0)) (So (n < 0)) -> Pint
intToPint' n (Left n_nonneg) = (integerToNat n, Z)
intToPint' n (Right n_neg) = (Z, integerToNat (negate n))

total
pintAdd : Pint -> Pint -> Pint
pintAdd (a, b) (c, d) = (a + c, b + d)

total
pintMult : Pint -> Pint -> Pint
pintMult (a, b) (c, d) = pintAdd (a * c, a * d) (b * d, b * c)

total
Num Pint where
  (+) = pintAdd
  (*) = pintMult
  fromInteger = intToPint

total
Neg Pint where
  negate = pintNegate
  a - b = a + negate b


-- verifiable Num instance
-- interface VerifiedRing a where
--   add : a -> a -> a
--   mult : a -> a -> a
--   fromInteger : Integer -> a
--   negate : a -> a

  -- properties to be proven
  -- comm : {x, y: a} -> (x `add` y = y `add` x)
  -- assoc : {x, y, z: a} -> (x `add` (y `add` z) = (x `add` y) `add` z)
  -- addId : let z = fromInteger 0

  --- more later


-- proofs
total
int2Pint2Int : (xi: Integer) -> (pintToInt (intToPint xi) = xi)
int2Pint2Int xi = ?ah

-- total
-- pintPreservesInt : (n: Integer) 
--                 -> (evid: Either (So (n >= 0)) (So (n < 0))) 
--                 -> pintToInt (intToPint' n evid) = n
-- pintPreservesInt n (Left n_nonneg) = ?wtf1
-- pintPreservesInt n (Right n_neg) = ?wtf2
total
eqPairs : {a1, a2: t} -> {b1, b2: v} -> a1 = a2 -> b1 = b2 -> (a1,b1) = (a2,b2)
eqPairs a1_eq_a2 b1_eq_b2 = trans (cong (,b1) a1_eq_a2) (cong (a2,) b1_eq_b2)

total
twocong : (f: a -> b -> x) -> (a1 = b1) -> (a2 = b2) -> (f a1 a2 = f b1 b2)
twocong f a1_eq_b1 a2_eq_b2 = rewrite (sym a2_eq_b2) in cong ($ a2) (cong f a1_eq_b1) 

intAdd : Integer -> Integer -> Integer
intAdd = prim__add_Integer

-- pintAddPreserves : (xp: Pint)  -> (yp: Pint) -> 
--   (pintToInt (pintAdd xp yp) = intAdd )

total
intAddIsPintAdd : (xi : Integer) -> (yi: Integer) -> 
  ((pintToInt $ pintAdd (intToPint xi) (intToPint yi)) = intAdd xi yi)
intAddIsPintAdd xi yi = 
  let xip = int2Pint2Int xi
      yip = int2Pint2Int yi
      pintsum_eq_intsum = int2Pint2Int (intAdd xi yi)
      wtf = twocong intAdd xip yip
      uhh = trans pintsum_eq_intsum (sym wtf)
  in  ?hello

total
pintAddCommutes : (x: Pint) -> (y: Pint) -> (x `pintAdd` y = y `pintAdd` x)
pintAddCommutes (a,b) (c,d) = eqPairs (plusCommutative a c) (plusCommutative b d)


total
integerAddCommutes : (xi : Integer) -> (yi : Integer) -> (xi + yi = yi + xi)
integerAddCommutes xi yi = 
  let pintAdd_xp_yp_eq_pintAdd_yp_xp = cong pintToInt $ pintAddCommutes (intToPint xi) (intToPint yi)
      pintAdd_yp_xp_eq_intAdd_yi_xi = intAddIsPintAdd yi xi
      pintAdd_xp_yp_eq_intAdd_xi_yi = intAddIsPintAdd xi yi
  in rewrite sym pintAdd_yp_xp_eq_intAdd_yi_xi
  in rewrite sym pintAdd_xp_yp_eq_intAdd_xi_yi
  in pintAdd_xp_yp_eq_pintAdd_yp_xp