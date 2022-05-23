module InsSort
-- Insertion sort with proof of correctness (at least, a proof of sortedness.)
-- TODO lift the So (isSortedAsc l) into a datatype-level statement on a list?

import Data.So    -- So, Oh, choose, andSo, soAnd

-- the basic version of the insert operation without proof terms. not actually
-- used anywhere, only for reference when writing the proof-carrying version
total
inssortInsert : (Ord a) => a -> List a -> List a
inssortInsert x [] = [x]
inssortInsert x (s::ss) = if x <= s then (x::s::ss) else s :: inssortInsert x ss

-- predicate to determine whether a list is sorted
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


-- some derived properties we can prove from the above axioms.

-- UNUSED
-- -- The permutation relation is symmetric: if xs is a permutation of ys then
-- -- ys is a permutation of xs
-- total
-- permutsSym : Permuts xs ys -> Permuts ys xs
-- permutsSym PermutsNils = PermutsNils
-- permutsSym (PermutsCons e prf) = PermutsCons e $ permutsSym prf
-- permutsSym (PermutsFlipCons d e prf) = PermutsFlipCons e d $ permutsSym prf
-- permutsSym (PermutsTrans prfa prfb) = PermutsTrans (permutsSym prfb) (permutsSym prfa)


-- The permutation relation is reflexive: A list is a permutation of itself.
total
permutsRefl : (xs: List a) -> Permuts xs xs
permutsRefl [] = PermutsNils
permutsRefl (e::es) = PermutsCons e (permutsRefl es)


-- A helper lemma that is useful later in the proof for insertion.
-- Lemma: If (s :: ss) is a permutation of ys, then (s :: x :: ss) is 
-- a permutation of (x :: ys).
total
permutsInsert : {x,s,ss:_} -> Permuts (s::ss) ys -> Permuts (s::x::ss) (x::ys)
permutsInsert prf = let
  permuts_x_s_ss___x_ys = PermutsCons x prf -- first cons both sides with x
  permuts_s_x_ss___x_s_ss = PermutsFlipCons s x (permutsRefl ss)
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


-- isn't this kind of like an "fmap" motive. cool tech; to be used in the
-- motive for inssortInsertWithProofs, below
total
mapHeadMotive : Ord a => (l : List a) -> (a -> Type) -> Type
mapHeadMotive [] head_mot = ()   -- when this is the case, this mot is irrelevant
mapHeadMotive (x :: xs) head_mot = head_mot x


{- 
the logic behind this motive for the proof-carrying insertion function is that:
  - the base case doesn't need to take any extra arguments, it merely
    provides proof that the empty list is sorted after insertion.
  - the inductive case, on the other hand, needs an argument that
    represents the inductive hypothesis, passed along from a previous recurse.
    The inductive hypothesis is a proof that the list being inserted into is 
    sorted. This is the So (isSortedAsc (s::ss)).

Having received this as hypothesis, an induction step will return:
    + the result of insertion, the list l  (as the first item of a DPair)
    + a proof that l is sorted;
    + a proof that l is a permutation of the list we would obtain if we merely
        cons'd the insertion-element at the front of the insertion-target-list.
        (i.e. "insert x ys" is a permutation of (x::ys)). This will build
        towards the proof that the result of insertion sort is a permutation of
        the original list.
    + a proof that the head of l (the "newhead") is either the old head
    (here "s") or the element just inserted (here "x"). 
        This provides proof for the insertion case where s <= x with the result 
        s :: (ins x (s2::ss)). There, as part of the isSortedAsc proof, we need 
        to show that s <= the head of (ins x (s2 :: ss)), and since in that 
        situation we always have both s <= x and s <= s2, and using this extra 
        proof term we have that the newhead is always either x or s2, we can 
        thus use the eitherEqsElim function to just "eliminate the disjunction" 
        into the thing we need, which is that s <= the newhead (which in that 
        part of the insertion function is called "r_x".)
-}
total
inssortInsertProofMotive : (a: Type) -> (x: a) -> (l: List a) -> Type
inssortInsertProofMotive a x [] = Ord a => (l: List a ** (So (isSortedAsc l), Permuts [x] l))
inssortInsertProofMotive a x (s::ss) = Ord a => 
  So (isSortedAsc (s::ss)) ->   -- to request the inductive hyp
    (l: List a ** (So (isSortedAsc l), Permuts (x::s::ss) l,
      mapHeadMotive l (\newhead => Either (newhead = s) (newhead = x))))



-- when "rewrite _ in _" can't figure out the motive, we can feed the motive
-- directly like this...
total
eitherEqsElim : (mot: (u:_) -> Type) -> (mx: mot x) -> (my: mot y) -> Either (u = x) (u = y) -> mot u
eitherEqsElim mot mx my (Left u_eq_x) = replace {p=mot} (sym u_eq_x) mx
eitherEqsElim mot mx my (Right u_eq_y) = replace {p=mot} (sym u_eq_y) my


-- the bulk of the work. this both does the insertion operation, and provides
-- proof that after insertion is a sorted list, and that the new head
-- post-insertion is either the old head or the element just inserted. the name
-- of the game is to just case-analysis and let-bind the hell out of it as much
-- as possible to hand-hold the compiler so that it can be confident enough to
-- expand our definitions and give us as much information as possible, getting
-- out of the way the "obvious cases" (the ones where we can just say Oh, Refl,
-- etc) as much as possible. (in this case the big challenge was to force
-- expansions of the definition of isSortedAsc, because that's the only way to
-- prove this; this entails having as many top-level pattern-match cases as does
-- isSortedAsc. The other big lesson from this exercise is that "if expressions"
-- are useless in proofs, we literally can't do anything with them. The way to
-- deal with algorithms with "if" in it is to promote the if-condition to the
-- type level and pass that around / pattern match on its cases, like the
-- pattern matching on LEQs here.)
total
inssortInsertWithProofs : (x: a) -> (l: List a) -> inssortInsertProofMotive a x l
inssortInsertWithProofs x [] = ([x] ** (Oh, permutsRefl [x]))
inssortInsertWithProofs x [s] = \slist_sorted => case chooseLEQ x s of
  Left x_leq_s => ((x :: [s]) ** 
    (andSo (x_leq_s, slist_sorted), permutsRefl [x, s], Right Refl))
  Right s_leq_x => ((s :: [x]) ** 
    (andSo (s_leq_x, slist_sorted), PermutsFlipCons x s PermutsNils, Left Refl))
inssortInsertWithProofs x (s :: (s2 :: ss)) = \slist_sorted => case chooseLEQ x s of
  Left x_leq_s => ((x :: s :: (s2 :: ss)) ** 
    (andSo (x_leq_s, slist_sorted), permutsRefl (x::s::s2::ss), Right Refl))
  Right s_leq_x => let
    -- ideally we would have a (s_leq_s2, s2_ss_is_sorted) = soAnd slist_sorted
    -- line up here, so that we can just grab the (snd $ soAnd slist_sorted)
    -- item out right away, but that breaks the "assert_smaller" for some
    -- reason... >:[
    
    -- the assert_smaller (s::(s2::ss)) (s2::ss) is to convince the totality
    -- checker that s2::ss is smaller. honestly surprised it can't figure this
    -- one out...
    
    -- slist_sorted is the "inductive hypothesis", which provides proof of 
    -- (s <= s2) && isSortedAsc (s2 :: ss2), and "soAnd" can yield each side of
    -- that &&.
    (rec_out ** (rec_sorted_proof, rec_permuts_proof, rec_head_proof)) = 
      (inssortInsertWithProofs x $ assert_smaller (s :: (s2 :: ss)) (s2 :: ss)) 
      $ (snd $ soAnd slist_sorted)  
    
    s_leq_s2 = fst $ soAnd slist_sorted
    
    proof_terms = case rec_out of
        [] => (Oh, permutsInsert rec_permuts_proof, Left Refl)
        (r_x :: r_xs) => let
            -- here, we prove that s <= r_x. This follows from the fact that we
            -- have s <= x (from the LEQs case analysis) and s <= s2 (from the
            -- inductive hypothesis, i.e. slist_sorted),
            -- and we can unite these cases with the knowledge that
            -- r_x is always either s2 or x (from rec_head_proof) to obtain just
            -- that s <= r_x.
            -- (also: replace is VERY particular about how it receives the
            -- motive. we can't just give the motive a name somewhere else
            -- and sub that name in here. it HAS to be this expression verbatim,
            -- otherwise idris can't figure out that this motive lambda expr
            -- applied to x or s2 is supposed to mean the same thing as 
            -- applying that name to x or s2, which is pretty sad)
            s_leq_r_x = eitherEqsElim (\rhs => So (s <= rhs)) s_leq_s2 s_leq_x rec_head_proof
          in (andSo (s_leq_r_x, rec_sorted_proof), permutsInsert rec_permuts_proof, Left Refl)
    in ((s :: rec_out) ** proof_terms)


-- run insertion sort, carrying proofs
total
inssortWithProofs : Ord a => (o: List a) -> (l: List a ** (So (isSortedAsc l), Permuts o l))
inssortWithProofs [] = ([] ** (Oh, PermutsNils))
inssortWithProofs [x] = ([x] ** (Oh, permutsRefl [x]))
inssortWithProofs (x::s::ss) =

  -- recursively sort (s :: ss); the resulting output and proof terms are our
  -- inductive hypotheses.
  let (inductive_out ** (inductive_sorted_proof, inductive_permuts_proof)) = 
    inssortWithProofs (s :: ss) 

  -- match on all the cases of the output of this inductive hypothesis:
  in case inductive_out of

    -- this case is actually unreachable, since the inductive sort on (s::ss)
    -- would never actually return [], but we can pretend that it can happen
    -- and give it a proof using our inductive hypothesis anyway!
    [] => ([x] ** (Oh, PermutsCons x inductive_permuts_proof))
    
    -- in this case, (r_x::r_xs) is the result of the recursive sort on (s::ss).
    (r_x :: r_xs) => let    
      -- insert x into the inductive sort result, giving us these output and
      -- proof terms....
      (insertion_result ** (insertion_sorted_prf, insertion_permuts_proof, _)) = 
          inssortInsertWithProofs x inductive_out inductive_sorted_proof
      
      -- insertion_permuts_proof is a proof that (x :: r_x :: r_xs) is a
      -- permutation of the insertion result.  
      -- What we need for the return value is a proof that 
      -- (x :: s :: ss) is a permutation of the insertion result, too. We can
      -- get to that through these steps:

      -- proof that (x :: s :: ss) is a permutation of (x :: r_x :: r_xs)
      permuts_x_s_ss___x_rx_rxs = PermutsCons x inductive_permuts_proof

      -- proof that (x :: s :: ss) is a permutation of the insertion result.
      -- this is what gets returned in the main insertion sort run.
      permuts_x_s_ss___insertion_result = PermutsTrans
          permuts_x_s_ss___x_rx_rxs insertion_permuts_proof
      
      -- uncomment this hole to check out the types of all the above...
      -- wow = ?wow

      in  (insertion_result ** 
            (insertion_sorted_prf, permuts_x_s_ss___insertion_result))

-- a version that just runs the sort and throws away the proof term
total
inssort : (Ord a) => List a -> List a
inssort original = fst $ inssortWithProofs original