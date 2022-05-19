module InsSort
-- Insertion sort with proof of correctness (at least, a proof of sortedness.)
-- (TODO: a proof that the sorted list has the same elements as the original)
-- (ALSO checking :t snd $ inssort_with_prf in the REPL gives a huge ugly
--    expression, instead of So True or So (isSortedAsc <a concrete list>).
-- is this okay??? I hope I have actually proven sth.. )

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

-- a type that represents the property that either (x <= y) or (y <= x)
-- (equality is taken to be Left)
total
LEQs : Ord a => (x: a) -> (y: a) -> Type
LEQs x y = Either (So (x <= y)) (So (y <= x))

-- construct a LEQs
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
-- motive for inssort_insrt_prf, below
total
map_head_mot : Ord a => (l : List a) -> (a -> Type) -> Type
map_head_mot [] head_mot = ()   -- when this is the case, this mot is irrelevant
map_head_mot (x :: xs) head_mot = head_mot x

{- 
the logic behind this motive for the proof-carrying insertion function is that:
  - the base case doesn't need to take any extra arguments, it merely
    provides proof that the empty list is sorted after insertion.
  - the inductive case, on the other hand, needs an argument that
    represents the inductive hypothesis, passed along from a previous recurse.
    The inductive hypothesis is a proof that the list being inserted into is 
    sorted; this is the So (isSortedAsc (s::ss)).

Having received this as hypothesis, an induction step will return:
    + the result of insertion, the list l  (as the first item of a DPair)
    + a proof that l is sorted;
    + a proof that the head of l (the "newhead") is either the old head
    (here "s") or the element just inserted (here "x"). 
    This provides proof for the insertion case where s <= x with the result 
    s :: (ins x (s2::ss)). There, as part of the isSortedAsc proof, we need to
    show that s <= the head of (ins x (s2 :: ss)), and since in that situation
    we always have both s <= x and s <= s2, and using this extra proof term
    we have that the newhead is always either x or s2, we can thus use the
    eitherEqsElim function to just "eliminate the disjunction" into the thing
    we need, which is that s <= the newhead (which in that part of the
    insertion function is called "r_x".)
-}
total
inssort_insrt_prf_mot : (a: Type) -> (x: a) -> (l: List a) -> Type
inssort_insrt_prf_mot a x [] = Ord a => (l: List a ** So (isSortedAsc l))
inssort_insrt_prf_mot a x (s::ss) = Ord a => 
  So (isSortedAsc (s::ss)) ->   -- to request the inductive hyp
    (l: List a ** (So (isSortedAsc l), 
      map_head_mot l (\newhead => Either (newhead = s) (newhead = x))))



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
inssort_insrt_prf : (x: a) -> (l: List a) -> inssort_insrt_prf_mot a x l
inssort_insrt_prf x [] = ([x] ** Oh)
inssort_insrt_prf x [s] = \slist_sorted => case chooseLEQ x s of
  Left x_leq_s => ((x :: [s]) ** (andSo (x_leq_s, slist_sorted), Right Refl))
  Right s_leq_x => ((s :: [x]) ** (andSo (s_leq_x, slist_sorted), Left Refl))
inssort_insrt_prf x (s :: (s2 :: ss)) = \slist_sorted => case chooseLEQ x s of
  Left x_leq_s => ((x :: s :: (s2 :: ss)) ** (andSo (x_leq_s, slist_sorted), Right Refl))
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
    (rec_out ** (rec_sorted_proof, rec_head_proof)) = (inssort_insrt_prf x $ 
      assert_smaller (s :: (s2 :: ss)) (s2 :: ss))  
        (snd $ soAnd slist_sorted)  
    s_leq_s2 = fst $ soAnd slist_sorted
    proof_terms = case rec_out of
        [] => (Oh, Left Refl)
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
          in (andSo (s_leq_r_x, rec_sorted_proof), Left Refl)
    in ((s :: rec_out) ** proof_terms)


-- run insertion sort, carrying proofs
total
inssort_with_prf : (Ord a) => List a -> (l: List a ** (So (isSortedAsc l)))
inssort_with_prf [] = ([] ** Oh)
inssort_with_prf [x] = ([x] ** Oh)
inssort_with_prf (x::s::ss) =
  let (rec_out ** rec_prf) = inssort_with_prf (s :: ss) 
  in case rec_out of
    [] => inssort_insrt_prf x []
    (r_x :: r_xs) => let        -- throw away the head-either-equality proof
      (ins_result ** (ins_sorted_prf, _)) = 
          inssort_insrt_prf x rec_out rec_prf
      in (ins_result ** ins_sorted_prf)

-- a version that just runs the sort and throws away the proof term
total
inssort : (Ord a) => List a -> List a
inssort = fst . inssort_with_prf