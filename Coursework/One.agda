------------------------------------------------------------------------
-- CS410 Advanced Functional Programming 2020
--
-- Coursework 1
------------------------------------------------------------------------

module Coursework.One where

----------------------------------------------------------------------------
-- COURSEWORK 1 -- WARMING UP, LOGIC, AND THE MATHEMATICAL STRUCTURE OF VECTORS
--
-- VALUE:     30% (divided over 60 marks, ie each mark is worth 0.5%)
-- DEADLINE:  5pm, Monday 12 October (Week 4)
--
-- SUBMISSION: Create your own clone of CS410 repo somewhere of your
-- choosing (e.g. Gitlab, Github, or Bitbucket), and let Fred know
-- where, so that you can invite the CS410 team to the project. The
-- last commit before the deadline is your submitted version. However
-- do get in touch if you want to negotiate about extensions.
----------------------------------------------------------------------------

-- HINT: These are all the imports from the standard library that you
-- should need, although you might of course have to define your own
-- auxiliary functions.

open import Data.Bool        using (Bool; true; false; not)
open import Data.Nat         using (ℕ; zero; suc; _<ᵇ_; _+_)
open import Data.List        using (List; []; _∷_; [_])
open import Data.Vec         using (Vec; []; _∷_; lookup)
open import Data.Fin         using (Fin; zero; suc)
open import Data.Product     using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Data.Empty       using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- HINT: your tasks are labelled with the very searchable tag '???'

-- TIP: When you load this file, you will see lots of open goals. You
-- can focus on one at a time by using comments {- ... -} to switch
-- off the later parts of the file until you get there.

------------------------------------------------------------------------
-- SOME GOOD OLD FUNCTIONAL PROGRAMMING: TREESORT (15 MARKS in total)
------------------------------------------------------------------------

{- ??? 1.1 Implement concatenation for lists.
   (1 MARK) -}

_++_ : {X : Set} -> List X -> List X -> List X
xs ++ ys = {!!}

infixr 5 _++_

-- a datatype of node-labelled binary trees is given as follows

data Tree (X : Set) : Set where
  leaf : Tree X
  _<[_]>_ : Tree X -> X -> Tree X -> Tree X

{- ??? 1.2 Implement the insertion of a number into a tree, ensuring that
       the numbers in the tree are in increasing order from left to right;
       make sure to retain duplicates.
   (2 MARKS) -}

insertTree : ℕ -> Tree ℕ -> Tree ℕ
insertTree = {!!}

-- HINT: the import list for Data.Nat above might contain useful things

{- ??? 1.3 Implement the function which takes the elements of a list and
       builds an ordered tree from them, using insertTree.
   (1 MARK) -}

makeTree : List ℕ -> Tree ℕ
makeTree xs = {!!}

{- ??? 1.4 Implement the function which flattens a tree to a list,
       using concatenation.
   (2 MARKS) -}

flatten : {X : Set} -> Tree X -> List X
flatten t = {!!}

{- ??? 1.5 Using the above components, implement a sorting algorithm which
       works by building a tree and then flattening it.
   (1 MARK) -}


treeSort : List ℕ -> List ℕ
treeSort xs = {!!}

-- TIP: You can uncomment the following test cases to check your work. They
-- should all typecheck if you got it right.

{-
_ : treeSort [ 1 ] ≡ [ 1 ]
_ = refl

_ : treeSort (1 ∷ 2 ∷ 3 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : treeSort (3 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : treeSort (3 ∷ 2 ∷ 3 ∷ []) ≡ (2 ∷ 3 ∷ 3 ∷ [])
_ = refl
-}

{- ??? 1.6 implement a fast version of flatten, taking an accumulating
       parameter, never using ++. It should satisfy

          fastFlatten t xs ≡ flatten t ++ xs

   (2 MARKS) -}

fastFlatten : {X : Set} -> Tree X -> List X -> List X
fastFlatten = {!!}

{- ??? 1.7 use fastFlatten to build a fast version of tree sort.
   (1 MARK) -}

fastTreeSort : List ℕ -> List ℕ
fastTreeSort xs = {!!}

-- TIP: You can copy and modify the test cases above to check that
-- also fastTreeSort works as intended.

{- ??? 1.8 *Prove* that fastFlatten correctly implements it
       specification.  You will need to prove an additional fact about
       concatenation separately, and use that in the proof.
   (3 MARKS) -}


fastFlattenCorrect : {X : Set} -> (t : Tree X) -> (xs : List X) ->
                     fastFlatten t xs ≡ (flatten t ++ xs)
fastFlattenCorrect = {!!}

{- ??? 1.9 Use fastFlattenCorrect to prove that treeSort and
       fastTreeSort agree. Again, you will need to prove an additional
       fact about concatenation.
   (2 MARKS) -}


fastTreeSortCorrect : (xs : List ℕ) -> fastTreeSort xs ≡ treeSort xs
fastTreeSortCorrect = {!!}

------------------------------------------------------------------------
-- LET'S BE LOGICAL (25 MARKS in total)
------------------------------------------------------------------------

variable
  P Q R : Set -- these are automatically introduced in types below

{- ??? 1.10 Implement the following operations:
   (1 MARK) -}

curry : (P × Q -> R) -> P -> Q -> R
curry = {!!}

uncurry : (P -> Q -> R) -> P × Q -> R
uncurry = {!!}

{- ??? 1.11 Implement the following operations:
   (2 MARKS) -}

orAdjunctionFrom : (P ⊎ Q -> R) -> ((P -> R) × (Q -> R))
orAdjunctionFrom = {!!}

orAdjunctionTo : {P Q R : Set} → ((P -> R) × (Q -> R)) -> (P ⊎ Q -> R)
orAdjunctionTo = {!!}

{- ??? 1.12 In Agda (and constructive logic in general), it is not
       possible to remove double negations. However, show that
       *triple* negations can be eliminated in the following sense:
   (1 MARK) -}

tripleNegationElimination : ¬ ¬ ¬ P -> ¬ P
tripleNegationElimination = {!!}

{- ??? 1.13 Similarly, show that even though the Law of Excluded
       Middle is not provable in Agda, the double-negation of it is.
   (2 MARKS) -}

¬¬LEM : {X : Set} -> ¬ ¬ (X ⊎ ¬ X)
¬¬LEM = {!!}

{- ??? 1.14 Show that the Law of Excluded Middle is logically
       equivalent to so-called Peirce's Law, ie the two principles
       imply each other.
   (5 MARKS) -}

Peirce→LEM : ({X Y : Set} -> ((X -> Y) -> X) -> X) -> ({X : Set} -> X ⊎ ¬ X)
Peirce→LEM = {!!}

LEM→Peirce : ({X : Set} -> X ⊎ ¬ X) -> ({X Y : Set} -> ((X -> Y) -> X) -> X)
LEM→Peirce = {!!}

{- ??? 1.15 For each of the following operations, either give an
       implementation, or comment it out and leave a comment
       explaining why it is impossible to implement.
   (4 MARKS) -}

deMorgan-⊎-from : ¬ (P ⊎ Q) -> (¬ P) × (¬ Q)
deMorgan-⊎-from = {!!}

deMorgan-⊎-to : (¬ P) × (¬ Q) -> ¬ (P ⊎ Q)
deMorgan-⊎-to = {!!}

deMorgan-×-from : ¬ (P × Q) -> (¬ P) ⊎ (¬ Q)
deMorgan-×-from = {!!}

deMorgan-×-to : (¬ P) ⊎ (¬ Q) -> ¬ (P × Q)
deMorgan-×-to = {!!}

{- ??? 1.16 Implement the following weakening of one of the de Morgan
       laws above:
   (2 MARKS) -}

¬¬deMorgan¬× : {P Q : Set} → ¬ (P × Q) -> ¬ ¬ ((¬ P) ⊎ (¬ Q))
¬¬deMorgan¬× = {!!}

{- ??? 1.17 Show that double negation is a /monad/; a concept you
       might remember from Haskell (don't worry if you don't, we'll
       get back to it later!). Concretely, you need to implement the
       following two operations:
   (1 MARK) -}

return : {P : Set} → P -> ¬ ¬ P
return = {!!}

_>>=_ : {P Q : Set} → ¬ ¬ P -> (P -> ¬ ¬ Q) -> ¬ ¬ Q
(¬¬p >>= f) ¬q = {!!}

-- TIP: if an operation with name _>>=_ is in scope, Agda allows us to
-- use do-notation (again possibly familiar from Haskell) to write
--
--    do
--      x <- mx
--      f
--
-- instead of mx >>= λ x → f. Here is an example (feel free to play
-- around and make a hole in the last line to see what is going on):

¬¬-map : {P Q : Set} -> (P -> Q) -> ¬ ¬ P -> ¬ ¬ Q
¬¬-map f ¬¬p = do
  p ← ¬¬p
  return (f p)

{- ??? 1.18 Use do-notation and/or ¬¬-map to show that
       double negation distributes over 'and' and 'or' (what about
       functions in the reverse directions?).
   (2 MARKS) -}

¬¬-distributes-× : ¬ ¬ P × ¬ ¬ Q -> ¬ ¬ (P × Q)
¬¬-distributes-× = {!!}

¬¬-distributes-⊎ : ¬ ¬ P ⊎ ¬ ¬ Q -> ¬ ¬ (P ⊎ Q)
¬¬-distributes-⊎ = {!!}

{- ??? 1.19 Moving on to predicate logic, show (one direction of) how
       'exists' commutes with 'or':
   (1 MARK) -}

∃-⊎-commutes : {A : Set}{P Q : A -> Set} ->
               (Σ A (λ a → P a ⊎ Q a)) ->
               (Σ A P) ⊎ (Σ A Q)
∃-⊎-commutes = {!!}

{- ??? 1.20 Similarly, show how we can push 'exists' inside 'forall':
   (1 MARK) -}

∃-∀-commutes : {A B : Set}{R : A -> B -> Set} ->
               Σ B (λ b → (a : A) -> R a b) ->
               ((a : A) ->  Σ B (λ b → R a b))
∃-∀-commutes = {!!}

{- ??? 1.21 But, show that it is false that we can push 'forall'
       inside 'exists', by instantiating A, B, and R appropriately.
   (3 MARKS) -}

not-∃-∀-commutes : ¬ ({A B : Set}{R : A -> B -> Set} ->
                      ((a : A) ->  Σ B (λ b → R a b)) ->
                      Σ B (λ b → (a : A) -> R a b))
not-∃-∀-commutes = {!!}

------------------------------------------------------------------------
-- THE RICH STRUCTURE OF VECTORS (20 MARKS in total)
------------------------------------------------------------------------

{- ??? 1.22 Implement concatenation for vectors. It's going to look a
       lot like concatenation for lists, except the type is more
       interesting.
   (1 MARK) -}

_++V_ : {n m : ℕ} -> {X : Set} -> Vec X n -> Vec X m -> Vec X (n + m)
xs ++V ys = {!!}

{- ??? 1.23 What about going in the reverse direction; every vector of
       length n + m should be the concatenation of a vector of length
       n and a vector of length m. This is indeed the case. Show this
       by implementing the following /view/ on vectors:
  (3 MARKS) -}

-- we use this datatype to express how we want to see such vectors
data Choppable {X : Set}(m n : ℕ) : Vec X (m + n) -> Set where
  chopTo : (xs : Vec X m)(ys : Vec X n) -> Choppable m n (xs ++V ys)

-- then we write a function which shows that all such vectors can be
-- seen that way
chop : {X : Set}(m n : ℕ)(xs : Vec X (m + n)) -> Choppable m n xs
chop = {!!}

{- ??? 1.24 Use the Choppable view to find the last element of an
       non-empty vector. Because addition is defined by looking at the
       first number, you probably want to rewrite first using the
       suc=+1 lemma (after proving it!).
   (2 MARKS) -}

suc=+1 : (n : ℕ) -> suc n ≡ n + 1
suc=+1 n = {!!}

last : {n : ℕ}{X : Set} -> Vec X (suc n) -> X
last = {!!}

{- ??? 1.25 Show how to make a constant vector of any given length.
   (1 MARK) -}

replicate : {n : ℕ} -> {X : Set} -> X -> Vec X n
replicate = {!!}

-- HINT: you may need to bring one of the implicit arguments into the spotlight

{- ??? 1.26 Show how one can take a vector full of functions and a
       vector full of inputs to create a vector full of outputs.
   (1 MARK) -}

_⊛_ : {n : ℕ}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
fs ⊛ as = {!!}

infixl 4 _⊛_

{- ??? 1.27 Implement map and zip for vectors using only replicate and
       _⊛_, ie without using pattern matching or recursion.
   (1 MARK) -}

vmap : {n : ℕ}{A B : Set} -> (A -> B) -> Vec A n -> Vec B n
vmap f = {!!}

vzip : {n : ℕ}{A B : Set} -> Vec A n -> Vec B n -> Vec (A × B) n
vzip as bs = {!!}


{- ??? 1.28 Show that vectors λ X → Vec X n, with pure = replicate and
       <*> = _⊛_, satisfies the laws for an Applicative:
   (4 MARKS) -}

vecAppIdentity : ∀ {n X}(xs : Vec X n) -> (replicate (λ y → y) ⊛ xs) ≡ xs
vecAppIdentity = {!!}

vecAppComposition : ∀ {n X Y Z} →
                    (fs : Vec (Y -> Z) n)(gs : Vec (X -> Y) n)(xs : Vec X n) ->
                    (replicate (λ f g x -> f (g x)) ⊛ fs ⊛ gs ⊛ xs) ≡  (fs ⊛ (gs ⊛ xs))
vecAppComposition = {!!}

vecAppHomomorphism : ∀ {n X Y}(f : X -> Y)(x : X) →
                     (replicate {n} (f x)) ≡ (replicate f ⊛ replicate x)
vecAppHomomorphism = {!!}

vecAppInterchange  : ∀ {n X Y}(fs : Vec (X -> Y) n)(x : X) ->
                      (fs ⊛ replicate x) ≡ (replicate (\ f -> f x) ⊛ fs)
vecAppInterchange = {!!}

{- ??? 1.29 Let's practice our vision for views by making one for
       vzip: every vector of pairs should arise as the zip of two
       vectors. First fill in the data needed for the view datatype
       below, and then implement unzip, hence giving evidence that you
       got it right.
   (3 MARKS) -}

data Unzippable {X Y : Set}{n : ℕ} : Vec (X × Y) n -> Set where
  unzipsTo : {! something goes here !} -> Unzippable {! something goes here !}

unzip : ∀ {n X Y} → (xs : Vec (X × Y) n) -> Unzippable xs
unzip = {!!}

{- ??? 1.30 There is also an alternative presentation of vectors as functions
       from finite types. Show how such functions correspond to vectors.
   (2 MARKS) -}

tabulate : {n : ℕ}{X : Set} → (Fin n -> X) -> Vec X n
tabulate = {!!}

-- HINT: Something interesting happens in the recursive call.

{- ??? 1.31 Show that tabulate is the inverse of
       lookup : Vec X n -> Fin n -> X, known already from the lecture
       in Week 1.
   (2 MARKS) -}

tabulate-lookup-identity : ∀ {n X}(xs : Vec X n) -> tabulate (lookup xs) ≡ xs
tabulate-lookup-identity = {!!}

lookup-tabulate-identity : ∀ {n X}(f : Fin n -> X)(x : Fin n) ->
                           lookup (tabulate f) x ≡ f x
lookup-tabulate-identity = {!!}
