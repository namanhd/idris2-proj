## Idris 2 project
*CMSC 22500 Spring 2022* 

#

## Proofs of correctness: Insertion sort and Bubble sort
This repo contains proof-carrying implementations of insertion sort
(`InsSort.idr`) and bubble sort (`BubbleSort.idr`). The proof terms carried
throughout the algorithms in dependent pairs prove the correctness of each
sorting algorithm alongside giving the actual sort result. This includes
- A proof that the output list is sorted
- A proof that the output list is a permutation of the original input list. 

The proofs are largely by induction, utilizing the invariants characteristic to
each sorting algorithm. The details are hairy, but the comments in the code
should have enough detail to walk one through the proof.

Written and working in Idris 2 (version 0.5.1); parts of the setup of the
proofs, including the definitions of sortedness and permutations, are adapted
from https://github.com/davidfstr/idris-insertion-sort; the rest of the proofs
are original.
<!-- 
## A bit of background
In a dependently-typed language like Idris 2, types can depend on value-level
expressions. Due to the Curry-Howard correspondence, this means that
(intuitionistic-logic-based) mathematical propositions can be encoded as types,
and their proofs encoded as values of these types. This allows languages with
dependent types to work as proof assistants (or at least, proof checkers), and
this is indeed how proof assistants like Coq and Agda work. Idris (here, Idris
2) is meant to be a general-purpose programming language with dependent types,
so even though it's morally designed for general programming, proving things in
it is also well-supported. -->