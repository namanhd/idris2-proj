module BubbleSort

import Data.So    -- So, Oh, choose, andSo, soAnd

data IsSorted : Ord a => List a -> Type where
  IsSortedEmpty : Ord a => IsSorted (the (List a) [])
  IsSortedSingleton : Ord a => (x:a) -> IsSorted [x]
  IsSortedMany : 
    Ord a => {x1, x2: a} -> {xs : List a} -> (So (x1 <= x2)) -> IsSorted (x2::xs) -> IsSorted (x1::(x2::xs))

-- derived properties from IsSorted
total
isSortedTail : Ord a => {x:a} -> {xs:List a} -> IsSorted (x::xs) -> IsSorted xs
isSortedTail (IsSortedSingleton x) = IsSortedEmpty
isSortedTail (IsSortedMany x1_leq_x2 x2_xs_sorted) = x2_xs_sorted

total
isSortedHeadLeq: Ord a => {x1,x2:a} -> {xs:List a} -> IsSorted (x1::x2::xs) -> So (x1 <= x2)
isSortedHeadLeq (IsSortedMany x1_leq_x2 x2_xs_sorted) = x1_leq_x2


-- predicate to determine whether a list is sorted (unused)
total
isSortedAsc : (Ord a) => List a -> Bool 
isSortedAsc [] = True
isSortedAsc [x] = True
isSortedAsc (x1::(x2::xs)) = (x1 <= x2) && isSortedAsc (x2 :: xs)


-- Axioms for the notion of two lists being permutations of one another. We're
-- leaving PTrans up here as an axiom for now, though later if we manage to
-- prove it from the first three only, we can then make it a function (a derived
-- property from these axioms.)

-- this can be read as:
-- Define Permuts a b as a statement about two lists that says 
-- 'list a is a permutation of list b' (i.e. a has the same elements as b,
-- just possibly in a different order)
data Permuts : List a -> List a -> Type where
  -- This relation should have the following axiomatic properties:
  -- 1. the empty list should be a permutation of the empty list
  PermutsNils : Permuts [] []
  -- 2. if xs is a permutation of ys then (e::xs) is a permutation of (e::ys)
  PermutsCons : (e: a) -> Permuts xs ys -> Permuts (e::xs) (e::ys)
  -- 3. if xs is a permutation of ys then (d::e::xs) is a permutation of (e::d::ys)
  PermutsFlipCons : (d: a) -> (e: a) -> Permuts xs ys -> Permuts (d::e::xs) (e::d::ys)
  -- 4. the permutation relation is transitive; if xs is a permutation of ys,
  -- and ys is a permutation of zs, then xs is a permutation of zs.
  PermutsTrans : Permuts xs ys -> Permuts ys zs -> Permuts xs zs
  -- there are probably a bunch more properties and ways to define the 
  -- permutation relation, but doing it this way makes it work well with the
  -- insertion algorithm in insertion sort. (actually this feels like it would
  -- go really well with the "merge" operation of mergesort too)

-- The permutation relation is reflexive: A list is a permutation of itself.
total
permutsRefl : {xs: List a} -> Permuts xs xs
permutsRefl {xs} = case xs of
  [] => PermutsNils
  (e::es) => PermutsCons e (permutsRefl)

-- A helper lemma that is useful later in the proof for insertion.
-- Lemma: If (s :: ss) is a permutation of ys, then (s :: x :: ss) is 
-- a permutation of (x :: ys).
total
permutsInsert : {x,s,ss:_} -> Permuts (s::ss) ys -> Permuts (s::x::ss) (x::ys)
permutsInsert prf = let
  permuts_x_s_ss___x_ys = PermutsCons x prf -- first cons both sides with x
  permuts_s_x_ss___x_s_ss = PermutsFlipCons s x permutsRefl
  in PermutsTrans permuts_s_x_ss___x_s_ss permuts_x_s_ss___x_ys



-- statement of the notion of either-Less-thans-or-Equalses. Can be expressed in
-- terms of more basic propositions, here Either and So, so we won't need to
-- define a new notion and a set of axioms using "data". 
total
LEQs : Ord a => (x: a) -> (y: a) -> Type
LEQs x y = Either (So (x <= y)) (So (y <= x))

-- For any two things with an ordering, either x <= y or y <= x.
total
chooseLEQ : Ord a => (x: a) -> (y: a) -> LEQs x y
chooseLEQ x y = case choose (x <= y) of
  Left oh_x_leq_y => Left oh_x_leq_y
  Right not_x_leq_y => case choose (y <= x) of
    Left oh_y_leq_x => Right oh_y_leq_x
    Right _ => believe_me "not x <= y implies x > y implies x >= y; impossible branch" 
    -- this branch never happens because a correct Ord implementation would
    -- never run into the case where neither x <= y nor y <= x is true. it's a
    -- little unsatisfying but we need this case too for totality, and we can't
    -- really frame this as Either (So (x <= y)) (So (x > y)) because there also
    -- is nothing in the Ord interface to make sure that a So (y < x) can be 
    -- cast into So (y <= x), so we would only be deferring this believe_me if
    -- we followed that approach.


-- basic version of bubble sort swap/bubble-up operation. only here for
-- reference when writing the proofful version
total
bubbleSwap : Ord a => List a -> List a
bubbleSwap [] = []
bubbleSwap [x] = [x]
bubbleSwap (x::s::ss) = if x > s 
  then s :: (bubbleSwap $ assert_smaller (x::s::ss) (x :: ss))
  else x :: (bubbleSwap $ assert_smaller (x::s::ss) (s :: ss))

-- basic version of bubble sort using the basic version of bubble swap.
-- "inductive hypothesis" is that (bubbleSort n list) assumes that list from
-- index n to the end is sorted!! (i.e. dropN (S n) is dropped) and after the
-- swap is run another time, the result is that the list now is sorted from
-- index (S n) to the end (i.e. dropN n is sorted) !!!!
total
bubbleSort : Ord a => Nat -> List a -> List a
bubbleSort Z list = list
bubbleSort (S n) list = bubbleSort n $ bubbleSwap list

-- this again
total
eitherEqsElim : (mot: (u:_) -> Type) -> (mx: mot x) -> (my: mot y) -> Either (u = x) (u = y) -> mot u
eitherEqsElim mot mx my (Left u_eq_x) = replace {p=mot} (sym u_eq_x) mx
eitherEqsElim mot mx my (Right u_eq_y) = replace {p=mot} (sym u_eq_y) my

-- To express the invariant for bubble sort's swap operation, we define dropN
-- which "drops at most n elements from the front of the list", bottoming out at
-- the empty list. The loop invariant of bubble sort swap is that a swap
-- operation assumes that the last m elements are in sorted order (i.e. dropN
-- (length - m) l is sorted), and after the swap operation, the assumption is
-- that now the last m+1 elements are in sorted order as well (i.e. dropN
-- (length - (S m)) is sorted). In more natural-numbery terms, that means
-- Swap assumes (dropN (S n) l) is sorted, and retuns that (dropN n l) is sorted.
total
dropN : Nat -> List a -> List a
dropN Z [] = []
dropN Z l = l
dropN (S n) [] = []
dropN (S n) (s :: ss) = dropN n ss

-- Some proofs about dropN that are useful

-- Dropping any number of items from an empty list gives the empty list
total
dropNEmptyIsEmpty : (n: Nat) -> ((dropN n []) = [])
dropNEmptyIsEmpty n = case n of 
  Z => Refl
  (S _) => Refl

-- ...and so any result that is the dropN of an empty list is sorted.
total
dropNEmptySorted : Ord a => (n: Nat) -> IsSorted  (dropN n (the (List a) []))
dropNEmptySorted n = rewrite cong (IsSorted {a}) $ dropNEmptyIsEmpty n in IsSortedEmpty

-- Dropping zero items from any list gives the same list
total
dropZeroIsSelf : (l: List a) -> (dropN 0 l = l)
dropZeroIsSelf l = case l of 
  [] => Refl
  (s::ss) => Refl 

-- ... and so if that list is already sorted, then dropping 0 items from it
-- still gives a sorted list.
total
dropZeroSorted : Ord a => (l: List a) -> IsSorted l -> IsSorted (dropN 0 l)
dropZeroSorted l prf = rewrite cong (IsSorted {a}) $ dropZeroIsSelf l in prf


-- these two proofs aren't used anywhere, but they're kind of neat.

-- This says: if dropN n returns a list of the form (s::ss), then 
-- dropN (S n) (i.e. dropping one more item) will return ss.
total
dropSnToList : {n, l, s, ss:_} -> (dropN n l = (s :: ss)) -> dropN (S n) l = ss
dropSnToList {n} {l} prf = case l of
  [] => let
    empty_is_s_ss = trans (sym $ dropNEmptyIsEmpty n) prf
    in cong (\l' => case l' of {(e::es) => es; [] => []}) empty_is_s_ss
  (x::xs) => case n of
    Z => let 
      xs_eq_ss = cong (\l' => case l' of {(e :: es) => es; [] => []}) prf 
      in trans (dropZeroIsSelf xs ) xs_eq_ss
    (S n') => dropSnToList prf


-- The other neat proof that is unused but can stay.
-- If dropN n l is sorted, then dropN (S n) l is also sorted (i.e. because
-- dropN (S n) l is just a sublist of dropN n l, since we drop more items).
total
dropnSortedImpliesDropSnSorted : Ord a => (n:_) -> (l: List a) -> 
  IsSorted (dropN n l) -> IsSorted (dropN (S n) l)
dropnSortedImpliesDropSnSorted n l dropnSorted = case n of
  Z => case l of
    [] => IsSortedEmpty
    (s::ss) => dropZeroSorted ss (isSortedTail dropnSorted)
  (S n') => case l of
    [] => IsSortedEmpty
    (s::ss) => dropnSortedImpliesDropSnSorted n' ss dropnSorted


-- synonyms for the types used in the proof of correctness of bubbleSwap

total
propIsSortedFrom : (a':_) -> Ord a' => (l: List a') -> (n: Nat) -> Type
propIsSortedFrom _ l n = IsSorted (dropN n l)

total
mapHeadMotive : Ord a => (l : List a) -> (a -> Type) -> Type
mapHeadMotive [] head_mot = ()   -- when this is the case, this mot is irrelevant
mapHeadMotive (x :: xs) head_mot = head_mot x

-- When a bubble-up operation (a swap) is run on (x::s::ss), the resulting list
-- will have a new head that is either x or s, and no other, because the only
-- thing that can happen at the head is either x is swapped with s, or it does
-- not get swapped. For inputs that are [x] then no swap will happen, so
-- we can directly return (newhead = x). For inputs that are [], then this
-- head identity is meaningless, so we do the () trick again to just provide
-- a trivial whatever-type we can trivially satisfy
total
propHeadSwapOrNoSwap : {a:_} -> Ord a => (o: List a) -> (l: List a) -> Type
propHeadSwapOrNoSwap o l = mapHeadMotive l $ \newhead => case o of
  [] => ()
  [x] => (newhead = x)
  (x :: s :: ss) => Either (newhead = x) (newhead = s)

total
bubbleSwapWithProof : Ord a => (n: Nat) -> (o: List a) -> propIsSortedFrom a o (S n) -> 
  (l ** (propIsSortedFrom a l n, Permuts o l, propHeadSwapOrNoSwap o l))
bubbleSwapWithProof n [] prf = ([] ** (dropNEmptySorted n, PermutsNils, MkUnit))
bubbleSwapWithProof Z [x] prf = ([x] ** (IsSortedSingleton x, permutsRefl, Refl))
bubbleSwapWithProof (S n) [x] prf_x_sorted = ([x] ** (dropNEmptySorted n , permutsRefl, Refl))
bubbleSwapWithProof Z (x :: s :: ss) s_ss_sorted = case chooseLEQ x s of
  Left x_leq_s => (x :: s :: ss ** (IsSortedMany x_leq_s s_ss_sorted, permutsRefl, Left Refl))
  Right s_leq_x => let
    ss_sorted = isSortedTail s_ss_sorted
    drop0_ss_sorted = rewrite cong (IsSorted {a}) $ dropZeroIsSelf ss in ss_sorted
    (rec_out ** (rec_sorted_proof, rec_permuts_proof, rec_head_proof)) = 
      bubbleSwapWithProof Z (assert_smaller (x::s::ss) (x :: ss)) drop0_ss_sorted
    -- this is where the propHeadSwapOrNoSwap is used...
    -- To obtain a proof that s <= r_x, we observe that the head of rec_out
    -- (where rec_out = bubbleSwap (x::ss)) is either x or the head of ss, since
    -- the only possibilities regarding the head of rec_out is either the
    -- head-of-ss got swapped with x or it didn't.
    -- And from chooseLEQ, we have that s <= x, and from s_ss_sorted, we'll also
    -- have that s <= head of ss. So we can unite the two cases
    proof_terms = case rec_out of
      [] => (IsSortedSingleton s, permutsInsert rec_permuts_proof, Right Refl)
      (r_x :: r_xs) => case ss of
          [] => let s_leq_r_x = rewrite rec_head_proof in s_leq_x 
            in (IsSortedMany s_leq_r_x rec_sorted_proof, permutsInsert rec_permuts_proof, Right Refl) 
          (s2 :: ss2) => let 
            s_leq_s2 = isSortedHeadLeq s_ss_sorted
            s_leq_r_x = eitherEqsElim (\rhs => So (s <= rhs)) s_leq_x s_leq_s2 rec_head_proof
            in (IsSortedMany s_leq_r_x rec_sorted_proof, permutsInsert rec_permuts_proof, Right Refl)
    in (s :: rec_out ** proof_terms)
bubbleSwapWithProof (S n) (x :: s :: ss) prf = case chooseLEQ x s of
  Left x_leq_s => let
    (rec_out ** (rec_sorted_proof, rec_permuts_proof, rec_head_proof)) = 
      bubbleSwapWithProof n (assert_smaller (x::s::ss) (s :: ss)) prf 
    proof_terms = case rec_out of
      [] => (dropNEmptySorted n, PermutsCons x rec_permuts_proof, Left Refl)
      (r_x :: r_xs) => (rec_sorted_proof, PermutsCons x rec_permuts_proof, Left Refl)
    in ((x :: rec_out) ** proof_terms)
  Right s_leq_x => let
    (rec_out ** (rec_sorted_proof, rec_permuts_proof, rec_head_proof)) = 
      bubbleSwapWithProof  n (assert_smaller (x::s::ss) (x :: ss)) prf
    proof_terms = case rec_out of
      [] => (rec_sorted_proof, permutsInsert rec_permuts_proof, Right Refl)
      (r_x :: r_xs) => (rec_sorted_proof, permutsInsert rec_permuts_proof, Right Refl)
    in ((s :: rec_out) ** proof_terms)


total
dropLengthIsEmpty : (l: List a) -> dropN (length l) l = []
dropLengthIsEmpty [] = Refl
dropLengthIsEmpty (e :: es) = dropLengthIsEmpty es

total
dropLengthSorted : Ord a => (l: List a) -> IsSorted (dropN (length l) l)
dropLengthSorted l = rewrite cong (IsSorted {a}) (dropLengthIsEmpty l) in IsSortedEmpty


-- can't have S n = length o for empty o, so we pull the slimy trick of case
-- matching in the type again, so that we can enforce a type but only when it's
-- available (i.e. we need (n = length es) but only when the list is of the form
-- (e::es).)
total
bubbleSortWithProofAdapter : Ord a => (n: Nat) -> (o: List a) -> 
  (case o of [] => (); (_::es) => Either (n = length es) (propIsSortedFrom a o (S n))) 
  -> (l ** (IsSorted l, Permuts o l))
bubbleSortWithProofAdapter n [] _ = ([] ** (IsSortedEmpty, PermutsNils))
bubbleSortWithProofAdapter n (e::es) some_ind_proof = let   
  -- "some_ind_proof" either provides the starter dropN-sortedness proof (in the
  -- Left case) which is (drop (length l) l = []) which implies IsSorted (drop
  -- (length l) l), or carries the sort proof from a previous recurse (in the
  -- Right case.)
  -- In either case we use this inductive hyp to seed/feed the swap operation...
  (swap_out ** (swap_sorted_proof, swap_permuts_proof, _)) = 
    bubbleSwapWithProof n (e::es) $ case some_ind_proof of
      (Left n_is_len_es) => rewrite n_is_len_es in dropLengthSorted (e::es)
      (Right sn_sorted) => sn_sorted
  in case n of
    -- this part here is basically the basic swap/bubble-up looper algo...
    -- If the counter number hits zero, just return the swap result,
    -- and if it's still nonzero, then do another bubble-up over the whole list
    Z => (swap_out ** (rewrite sym (dropZeroIsSelf swap_out) in swap_sorted_proof, 
      swap_permuts_proof))
    S n' => let 
      (rec_out ** (rec_sorted_proof, rec_permuts_proof)) = 
        bubbleSortWithProofAdapter n' swap_out $ 
          case swap_out of
            [] => MkUnit
            (_ :: _) => Right swap_sorted_proof
      in (rec_out ** (rec_sorted_proof, 
        PermutsTrans swap_permuts_proof rec_permuts_proof))
  
  
-- finally driver that runs the sort, providing all proof terms
-- (this is surprisingly involved, since we have to provide the right starting-
-- inductive hypothesis thingy to start it.)
total
bubbleSortWithProof : Ord a => (o: List a) -> (l: List a ** (IsSorted l, Permuts o l))
bubbleSortWithProof [] = bubbleSortWithProofAdapter 0 [] MkUnit
bubbleSortWithProof o@(x::xs) = bubbleSortWithProofAdapter (length xs) (x::xs) 
  (Left Refl) -- Left Refl provides proof that length xs == length xs. (i.e.
  -- initializes the starting counter number to length xs.)
