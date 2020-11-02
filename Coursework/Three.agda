{-# OPTIONS --type-in-type #-}
------------------------------------------------------------------------
-- CS410 Advanced Functional Programming 2020
--
-- Coursework 3
------------------------------------------------------------------------

module Coursework.Three where

----------------------------------------------------------------------------
-- COURSEWORK 3 -- BUILDING A STRUCTURED WINDOW MANAGER
--
-- VALUE:     40% (divided over 80 marks, ie each mark is worth 0.5%)
-- DEADLINE:  5pm, Monday 7 December (Week 12)
--
-- SUBMISSION: Push your solutions to your own repo. Your last commit
-- before the deadline is your submitted version. However do get in
-- touch if you want to negotiate about extensions.
----------------------------------------------------------------------------

-- HINT: your tasks are labelled with the very searchable tag '???'

-- TIP: I have split up this file into a bunch of commented out
-- sections named after Scottish islands. When you reach a new
-- section, you can search for it's corresponding end tag (Ctrl-s in
-- emacs) to comment it in and start working on it.

open import Category.Applicative  using (RawApplicative)
open import Data.Char             using (Char)
open import Data.String as String using (String; fromList)
open import Data.Nat              using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties   -- you can use it all!
open import Data.Bool             using (Bool; true; false; if_then_else_)
open import Data.List   as L      using (List; []; _∷_; map)
open import Data.List.Properties  using (map-id; map-compose)
open import Data.Vec   as V
  using (Vec; []; _∷_; _++_; replicate; map; splitAt) -- splitAt is `chop` from CW 1
open import Data.Product          using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; map)
open import Data.Sum   as Sum     using (_⊎_; inj₁; inj₂; map)
open import Data.Unit             using (⊤; tt)
open import Data.Empty            using (⊥; ⊥-elim)
open import Function   as F       using (_∘′_; id)
open import IO.Primitive          using (IO)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; cong-app; sym; trans; subst; module ≡-Reasoning)
open import Relation.Unary        using (Universal ; _⇒_; _∩_; _∪_)
open import Relation.Nullary      using (¬_)

open import Common.Category
open import Common.Category.Solver


------------------------------------------------------------------------------
--  Overture: A Very Simple Application (0 MARKS in total)
------------------------------------------------------------------------------

open import Common.Display

-- To get you started, here is a very simple application which you
-- will embellish during the course of the coursework.  If you make
-- sure all holes are commented out, you should be able to run this
-- now! All it does is fill the terminal with a given character
-- (Ctrl-C quits). See the very bottom of this file for instructions
-- how to compile and run the program.

-- You can look up the definition of the type Application in
-- Common.Display, or you can try to get the gist of it from this example
-- application.

rectApp : Char              -- character to display ("state" of the application)
       -> Π[ Application ]  -- an application of *any* screen size
-- To "display", an application must supply a pair of things:
proj₁ (display (rectApp c wh))       -- a matrix of coloured characters
  = replicate (replicate (green - c # black)) -- here, copies of character c
proj₂ (display (rectApp c wh))       -- the cursor position
  = wh -- here, the bottom right corner (= the size of the window)

-- To "react", an application must respond to events, which means giving
-- three things: (i) a new size, (ii) a proof that the new size is correct,
-- (iii) the new incarnation of the application.
-- What's the correct size?

--  When a key is pressed, the screen size must stay the same!
react (rectApp _ wh) (key (char c'))  -- a printable character was typed, so
  = wh , refl , rectApp c' wh  -- *preserve* screen size, switch to typed char
react (rectApp c wh) (key _)  -- another key was pressed, so
  = wh , refl , rectApp c wh  -- do nothing

--  When a resize happens, the screen size must become the demanded size!
react (rectApp c wh) (resize w h)
  = (w , h) , refl , rectApp c (w , h)


{- arran UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
--  Proofs for All (20 marks in total)
------------------------------------------------------------------------------

-- Before we get started building our own application, let us equip
-- ourselves with some mathematical kit. The All data type records
-- that a given property holds for all elements of a list:

data All {A : Set} (P : A -> Set) : List A -> Set where
  []  : All P []
  _∷_ : ∀ {x xs} → (px : P x) -> (pxs : All P xs) -> All P (x ∷ xs)


{- ??? 3.1 To get a feel for All, show that every element of list0
       and list1 is even, whilst every element of list2 is not:
   (2 MARKS)
-}

data IsEven : ℕ -> Set where
  zero : IsEven zero
  sucsuc : ∀ {n} → IsEven n -> IsEven (suc (suc n))

list0 list1 list2 : List ℕ
list0 = 2 ∷ 10 ∷ 6 ∷ []
list1 = 2 ∷ 16 ∷ 58 ∷ 156 ∷ 92 ∷ []
list2 = 2 ∷ 400 ∷ 5 ∷ 38 ∷ []

yesTheyAre : All IsEven list0
yesTheyAre = {!!}

isEven2*_ : (n : ℕ) -> IsEven (2 * n)
isEven2* n = {!!}

lifeIsToShortToProveThisByHand : All IsEven list1
lifeIsToShortToProveThisByHand = {!!}

noTheyArent : ¬ All IsEven list2
noTheyArent = {!!}


-----------------------
--  All is functorial
-----------------------

{- ??? 3.2 Show that All is a functor from I-indexed sets to List
       I-indexed sets.
   (1 MARK) -}

All-map : {I : Set}{P Q : I → Set} → Π[ P ⇒ Q ] → Π[ All P ⇒ All Q ]
All-map = {!!}

  {- ??? 3.3 Okay, now show that I-indexed sets form a category, and
         that All *really is* a functor from I-indexed sets to List
         I-indexed sets.
     (3 MARKS) -}

module _ where
  open Category
  open Functor

  _-C>_ : (I : Set) -> (C : Category) -> Category
  Obj (I -C> C) = I -> Obj C
  Hom (I -C> C) F G = {!!}
  Category.id (I -C> C) = {!!}
  comp (I -C> C) f g = {!!}
  assoc (I -C> C) = {!!}
  identityˡ (I -C> C) = {!!}
  identityʳ (I -C> C) = {!!}

  ALL : {I : Set} -> Functor (I -C> SET) (List I -C> SET)
  ALL = {!!}


{- ??? 3.4 Show that the functor ALL preserves finite products, ie All
       preserves (pointwise) ⊤ and (pointwise) ×.
   (2 MARKS) -}

-- HINT: Two of these work for any functor, and hence should not
-- require any pattern matching.

All-⊤ : {I : Set} -> Π[ All (λ (i : I) → ⊤) ⇒ (λ is → ⊤) ]
All-⊤ = {!!}

All-⊤⁻¹ : {I : Set} -> Π[ (λ is → ⊤) ⇒ All (λ (i : I) → ⊤) ]
All-⊤⁻¹ = {!!}

All-× : {I : Set}{P Q : I -> Set} -> Π[ All (P ∩ Q) ⇒ (All P ∩ All Q) ]
All-× = {!!}

All-×⁻¹ : {I : Set}{P Q : I -> Set} -> Π[ (All P ∩ All Q) ⇒ All (P ∩ Q) ]
All-×⁻¹ = {!!}


{- ??? 3.5 Show that All *does not* preserve either (pointwise) ⊥ or
       (pointwise) ⊎ in general, ie ALL does not preserve finite
       coproducts.
   (4 MARKS) -}

¬-All-⊥ : ¬ ({I : Set} -> Π[ All (λ (i : I) → ⊥) ⇒ (λ is → ⊥) ])
¬-All-⊥ claim = {!!}

¬-All-⊎ : ¬ ({I : Set}{P Q : I -> Set} -> Π[ All (P ∪ Q) ⇒ (All P ∪ All Q) ])
¬-All-⊎ claim = {!!}


-----------------------
--  Reindexing All
-----------------------

-- What is the relationship between
--   All (λ x → P (f x)) xs
-- and
--   All P (L.map f xs) ?
-- Both types say that P (f x) holds for every x in xs, but the types
-- are not obviously the same, so a proof is required to that effect.

-- Also note that in fact any
--   All P xs
-- can be seen as an
--   All P (L.map id xs)
-- because you know that L.map preserves id.


{- ??? 3.6 Extend "All-map" to allow reindexing. We can avoid using
       function extensionality (remember we want to run our program,
       so we can't have any postulates we do not know how to compile!)
       by only asking for exactly the equalities we need.
   (2 MARKS) -}

All-mapExt : ∀ {X I J}                          -- some index types
             {P : I -> Set}{Q : J -> Set}       -- we shall turn Ps into Qs

             (f : X -> I)                       -- we shall reindex P by f
             {mf : List X -> List I}            -- we have a copy of map f
             (mfEq : ∀ xs → L.map f xs ≡ mf xs)

             (g : X -> J)                       -- we shall reindex Q by g
             {mg : List X -> List J}            -- we have a copy of map g
             (mgEq : ∀ xs → L.map g xs ≡ mg xs)

         -> Π[      (P ∘′ f) ⇒      (Q ∘′ g) ]  -- we can turn Ps into Qs, so
         -> Π[ (All P ∘′ mf) ⇒ (All Q ∘′ mg) ]  -- turn (All P)s into (All Q)s!
All-mapExt f {mf} mfEq g {mg} mgEq pq xs ps with mf xs | mfEq xs | mg xs | mgEq xs
All-mapExt f {lf} lfEq g {lg} lgEq pq xs ps | ._ | refl | ._ | refl = {!!}


  {- ??? 3.7 Check that you can define the following "identity functions"
         by instantiating All-mapExt appropriately.
     (1 MARK)
  -}

module _ {X Y}(f : X -> Y){P : Y -> Set} where

  -- HINT: You might want to see what you can use from Data.List.Properties.

  allList : Π[ All (P ∘′ f) ⇒ (All P ∘′ L.map f) ]
  allList = {!!}

  allTsil : Π[ (All P ∘′ L.map f) ⇒ All (P ∘′ f) ]
  allTsil = {!!}

--------------------------
-- Applicative structure
--------------------------

-- Remember applicatives? In Coursework.One, you showed that Vectors
-- are applicative:

VApp : ∀ n -> RawApplicative (λ X -> Vec X n)
VApp n = record { pure = replicate ; _⊛_ = V._⊛_ }

-- As incidentally suggested by the name, we will have use of
-- applicative functors in the building of applications. Hence we need
-- to build up some applicative machinery for All:

  {- ??? 3.8 Show that you can yank applicative structure out through
         All.
     (2 MARKS)
  -}

module _ {F : Set -> Set}(ApF : RawApplicative F) where
  open RawApplicative ApF

  allYank : ∀ {X}{P : X -> Set} → Π[ All (F ∘′ P) ⇒ (F ∘′ All P) ]
  allYank = {!!}


{- ??? 3.9 Find the *indexed* applicative structure for All. (This
       sadly does not fit in the RawApplicative record of the standard
       library, as it is not formulated for arbitrary categories.)
   (1 MARK)
-}

-- HINT: this is very similar to what happens for vectors.

pureAll : ∀ {I}{P : I -> Set} → Π[ P ] -> Π[ All P ]
pureAll = {!!}

appAll  : ∀ {I}{P Q : I -> Set} → Π[ All (P ⇒ Q) ⇒ All P ⇒ All Q ]
appAll = {!!}


{- ??? 3.10 Implement transposition:
   (2 MARKS)
-}

-- HINTS:
-- (i)  This is a classic exercise in deploying applicative structure.
-- (ii) This is not just for fun; you will need this later.

transpose : {I J : Set}{R : I -> J -> Set}
            {is : List I}{js : List J}
  -> All (λ i → All (λ x → R i x) js) is  -- If every i is related to every j,
  -> All (λ j → All (λ x → R x j) is) js  -- show every j is related to every i.
transpose = {!!}

END OF COMMENT arran -}

{- barra UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
-- CODE FOR CUTTING UP THINGS (25 MARKS in total)
------------------------------------------------------------------------------

-- If we want to write a window manager, we need to subdivide, ie cut
-- up, the screen in different ways. Let us develop the tools to talk
-- about cuts in that way. The following definition can be used to
-- describe how an outside can be cut up into a finite list of inside
-- pieces:

record _<|_ (O{-utside-} I{-nside-} : Set) : Set where
  constructor _<!_
  field
    Cuts    : O -> Set  -- for every Outside, there is a set of ways to cut it
    pieces  : {o : O} -> Cuts o -> List I
                        -- into a bunch of pieces which are Inside
open _<|_

-- This is our runnning and motivating example:

NatCut : ℕ <| ℕ
Cuts NatCut z = Σ ℕ λ x → Σ ℕ λ y → (x + y) ≡ z
pieces NatCut (x , y , _) = x ∷ y ∷ []

-- See? To cut a natural number z, you choose two numbers x and y such
-- that their sum is z, and the pieces of such a cut is x and y
-- themselves.

-- The following "meaning" of cuts explains how one makes a cut, and
-- fill the resulting insides:

⟦_⟧Cr : {O I : Set} ->
        O <| I -> (I -> Set)   -- what's filling the insides?
               -> (O -> Set)
⟦ Cu <! ps ⟧Cr P o =      Σ (Cu o) λ c →  -- choose a way to cut o
                            All P (ps c)  -- then fill all the insides with P


{- ??? 3.11 For intuition, cut up 12 into two odd pieces.
   (1 MARK)
-}

cut12 : ⟦ NatCut ⟧Cr (¬_ ∘′ IsEven) 12
cut12 = {!!}


  {- ??? 3.12 Extend ⟦_⟧Cr to a functor.
    (2 MARKS) -}

  -- HINT: It's okay for you to use function extensionality here,
  -- because we won't need to run the proofs from this section in the
  -- final program. You might also find `cong-app`, the inverse of
  -- function extensionality, useful.

module _ {O I : Set} where

  open Functor

  ⟦_⟧CrF : (F : O <| I) ->
               Functor (I -C> SET) (O -C> SET)
  ⟦ Cu <! ps ⟧CrF = {!!}


------------------------------
-- Cutting and cutting again
------------------------------

module _ {I : Set}(F : I <| I) where

  -- The operation ⟦_⟧Cr let's us make one cut. If the insides have
  -- the same index type as the outsides, we can cut and cut again,
  -- using the following definition:

  data Tree (X : I -> Set)(i : I) : Set where
    leaf : X i -> Tree X i
    <_> : ⟦ F ⟧Cr (Tree X) i -> Tree X i

-- The following wrap the constructors as morphisms in I -C> SET.

  iLeaf : {X : I -> Set} -> Π[ X ⇒ Tree X ]
  iLeaf i = leaf

  iNode : {X : I -> Set} -> Π[ ⟦ F ⟧Cr (Tree X) ⇒ Tree X ]
  iNode i = <_>


{- ??? 3.13 Making *at least two cuts*, cut up 8 into many odd pieces.
   (1 MARK) -}

cut8 : Tree NatCut (¬_ ∘′ IsEven) 8
cut8 = {!!}

module _ {I : Set}(F : I <| I)
         {X Y : I -> Set}             -- Suppose we can turn ...
         (l : Π[ X ⇒ Y ])            -- ... leaves into Ys, and ...
         (n : Π[ ⟦ F ⟧Cr Y ⇒ Y ])  -- ... nodes made of Ys into Ys.
       where


  {- ??? 3.14 Show that we can turn whole trees into Ys.
    (2 MARKS) -}

  -- HINT: You will need to inline functoriality of All to get the
  -- termination checker to shut up.

  treeIter : Π[ Tree F X ⇒ Y ]
  treeIter = {!!}

{- ??? 3.15 Use treeIter, rather than pattern matching, to
       construct the following operation which should preserve
       nodes and graft on more tree at the leaves.
  (1 MARK) -}

treeBind : {I : Set}(F : I <| I){X Y : I -> Set} -> Π[ X ⇒ Tree F Y ] -> Π[ Tree F X ⇒ Tree F Y ]
treeBind F k = {!!}


{- ??? 3.16 Use treeBind to implement "map" and "join" for trees.
       They're one-liners.
   (1 MARK) -}

Tree-map : {I : Set}(F : I <| I){X Y : I -> Set} -> Π[ X ⇒ Y ] -> Π[ Tree F X ⇒ Tree F Y ]
Tree-map F f = {!!}

treeJoin : {I : Set}(F : I <| I){X : I -> Set} -> Π[ Tree F (Tree F X) ⇒ Tree F X ]
treeJoin F = {!!}


{- ??? 3.17 Show that replacing leaves by leaves and nodes by nodes does nothing.
  (2 MARKS) -}

-- HINT: You might want to do something simultaneous.

treeIterId : {I : Set}{F : I <| I}{X : I -> Set} -> treeIter F (iLeaf F {X = X}) (iNode F) ≡ λ i → id
treeIterId {I} {F} {X} = {!!}

module _ {I : Set}{F : I <| I} where

  -- The following result will be of considerable assistance.

  module _ {W X Y : I -> Set}
           (k : Π[ W ⇒ Tree F X ])   -- how to grow more tree
           (l : Π[ X ⇒ Y ])          -- how to eat leaves
           (n : Π[ ⟦ F ⟧Cr Y ⇒ Y ])  -- how to eat nodes
           where
    open Category (I -C> SET) hiding (_⇒_)


    {- ??? 3.18 Show that growing a tree with treeBind then eating the result
           gives the same as eating the original with more eating at the leaves.
      (3 MARK) -}

    -- HINT: This is similar to treeIterId.

    treeBindIter : comp (treeBind F k) (treeIter F l n)
                     ≡
                   treeIter F (comp k (treeIter F l n)) n
    treeBindIter = {!!}

  -- Suitably tooled up, go for the win.

  module _  where
    open Category (I -C> SET)
    open Functor
    open NaturalTransformation
    open Monad

    {- ??? 3.19 You have implemented "map" and "join".  Prove that you
           have a functor and a monad.
      (5 MARKS) -}

    TREE : Functor (I -C> SET) (I -C> SET)
    TREE = {!!}

    treeMonad : Monad (I -C> SET)
    treeMonad = {!!}

END OF COMMENT barra -}

{- colonsay UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------
--  Cutting in Multiple Dimensions
------------------------------------

-- If we know how to cut up numbers (seen as lengths), we ought to be able
-- to cut up pairs of numbers (see as the width and height of a rectangle).

-- Let's approach the problem in small steps.


{- ??? 3.20 Angelic choice of cutting. (Here "angelic" means *you* get
       to choose which sort of cut to make.)
   (2 MARKS)
-}

-- Specification:
-- (i)   We get two different schemes for cutting the same sort of "outer"
--       into "inner" pieces.
-- (ii)  Combine them by offering to cut in accordance with either scheme.
-- (iii) The pieces should then be those given for the chosen cut in the
--       chosen scheme.

_>+<_ : forall {O I} -> O <| I -> O <| I -> O <| I
((C <! ps) >+< (D <! qs)) = {!!}


{- ??? 3.21 Right and Left Framing.
   (2 MARKS)
-}

-- Specification:
-- These operators should generate higher dimensional cutting schemes
-- from some lower dimensional C,
-- by attaching an extra dimension, J,
-- which is never affected by a cut.
-- That is, the given value in O should determine the choice of cuts
-- according to C. All pieces should inherit the given value in J.


_>|_ : forall {O I}      (C : O <| I) J   ->      (O × J) <|     (I × J)
((C <! ps) >| J) = {!!}

_|<_ : forall {O I}    J (C : O <| I)     ->  (J × O)     <| (J × I)
(J |< (C <! ps)) = {!!}

-- Intuition:
-- If you know how to cut up a number into parts, then you know how to
-- cut up a rectangle whose width is that number into subrectangles
-- whose widths are the parts. The height of the original rectangle
-- is then the height of all of its parts.


{- ??? 3.22 Combining Separate Dimensions
   (2 MARKS)
-}

-- Specification:
-- (i)   We have two separate dimensions, indexed by I and J, respectively.
-- (ii)  We know, separately, a scheme for cutting each dimension.
-- (iii) We want a cutting scheme which allows us
--         either to cut the I dimension, preserving the J index,
--         or     to cut the J dimension, preserving the I index.

-- HINT: use framing and angelic choice, of course!

_|+|_ : forall {I J} -> I <| I -> J <| J -> (I × J) <| (I × J)
F |+| G = {!!}


-- Having taken those small steps, we now have a scheme for cutting up
-- rectangles with axis-aligned cuts, either somewhere along their
-- width or somewhere along their height.

RectCut : (ℕ × ℕ) <| (ℕ × ℕ)
RectCut = NatCut |+| NatCut


{- ??? 3.23 To make sure we know what is going on, tile a rectangular
       area with square pieces.
   (1 MARK)
-}

data Square : ℕ × ℕ -> Set where
  square : (n : ℕ) -> Square (n , n)

-- NOTE: you can't make a Square (w , h) unless w and h are equal.

-- Specification:
-- (i)   If your current goal has equal width and height, give a square leaf.
-- (ii)  Otherwise, cut your rectangle into two pieces, the first of which
--       is square.

example : Tree RectCut Square (10 , 6)
example = {!!}

-- If you ignore the specification, is this the only way to square the rectangle?

END OF COMMENT colonsay -}

{- danna UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE
------------------------------------------------------------------------------
--  After Cut Comes Paste (20 MARKS in total)
------------------------------------------------------------------------------

-- A notion of "cutting" induces a functor.
-- The corresponding algebras are "pasting" operators.

Pasting : forall {I}(C : I <| I)(X : I -> Set) -> Set
Pasting C X = Π[ ⟦ C ⟧Cr X ⇒ X ]


{- ??? 3.24 Find the component that gives vectors a pasting operator
       for NatCut in Data.Vec.
  (1 MARK)
-}

vecPaste : forall {X} -> Pasting NatCut (Vec X)
vecPaste = {!!}

-- We can now use the kit you built earlier to combine pasting
-- algebras for multiple dimensions:

compPaste : ∀ {I J}                -- What you get:
  -> (C : I <| I)(F : Set -> I -> Set)  -- C cuts correspond to F layers

  -> (D : J <| J)(G : Set -> J -> Set)  -- D cuts correspond to G layers
  -> (∀ j → RawApplicative λ X → G X j)  -- and G is always applicative

  -> (∀ {X} → Pasting C (F X))    -- polymorphic C-paster for F
  -> (∀ {X} → Pasting D (G X))    -- polymorphic D-paster for G
                                        -- What we want:
  -> (∀ {X} → Pasting (C |+| D) (λ { (i , j) -> G (F X i) j}))
     -- a polymorphic two-dimensional paster for Gs of Fs
compPaste C F D G ApG cf dg (i , j) (inj₁ c , ps)
  = pure (cf i) ⊛ (pure (c ,_) ⊛ allYank (ApG j) _ (allTsil _ _ ps))
  where open RawApplicative (ApG j)
compPaste C F D G ApG cf dg (i , j) (inj₂ d , ps)
  = dg j (d , allTsil _ _ ps)


{- ??? 3.25 Use compPaste to give a one-line RectCut-paster for Matrix
       (from Common.Display) dimensions.
   (1 MARK)
-}

matPaste : ∀ {X} → Pasting RectCut (Matrix X)
matPaste = {!!}


{- ??? 3.26 In one line, using previous components but no pattern
       matching, show how to paste together a Matrix from a tree whose
       leaves each map to a Matrix.
  (1 MARK)
-}

treeMatrix : ∀ {X P} → Π[ P ⇒ Matrix X ] -> Π[ Tree RectCut P ⇒ Matrix X ]
treeMatrix = {!!}


----------------------
--  Seeing the Matrix
----------------------

-- This is for entertainment and a chance to breathe, and to check your work.

-- Here's a function to draw an ascii-art square of a given size.

squareChar : Π[ Square ⇒ Matrix Char ]
squareChar _ (square zero)          = []
squareChar _ (square (suc zero))    = ('#' ∷ []) ∷ []
squareChar _ (square (suc (suc i))) rewrite +-comm 1 i
  =  (',' ∷ replicate '-' V.++ '.' ∷ [])              --   ,-.
  ∷ replicate ('|' ∷ replicate ' ' V.++ '|' ∷ [])     --   | |
  V.++ ('`' ∷ replicate '-' V.++ '\'' ∷ [])           --   `-'
  ∷ []

-- You can flatten a matrix of characters to a list of strings.
showMatrix : forall {wh} -> Matrix Char wh -> List String
showMatrix = L.map (String.fromList ∘′ V.foldr _ _∷_ []) ∘′ V.foldr (λ _ → List (Vec Char _)) _∷_ []

-- Let's get the matrix from your earlier example Tree of Squares.
exampleMatrix : Matrix Char (10 , 6)
exampleMatrix = treeMatrix squareChar (10 , 6) example

-- It should look like this.
expectedOutput : List String
expectedOutput =
  ",----.,--." ∷
  "|    ||  |" ∷
  "|    ||  |" ∷
  "|    |`--'" ∷
  "|    |,.,." ∷
  "`----'`'`'" ∷ []

-- Does it?
checkOutput : showMatrix exampleMatrix ≡ expectedOutput
checkOutput = {!!}

END OF COMMENT danna -}

{- eriskay UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE
--------------------
-- The List Relator
--------------------

-- While we are still relaxing, let us collect some more down-to-Earth
-- marks by considering the *relational* action of lists. ListR, the
-- List "Relator", lifts a binary relation on elements to a binary
-- relation on lists of elements. This is like All, but for relations,
-- not predicates.

data ListR {X Y : Set}(R : X -> Y -> Set) : List X -> List Y -> Set where
  []   : ListR R [] []
  _∷_ : ∀ {x xs y ys} → R x y -> ListR R xs ys -> ListR R (x ∷ xs) (y ∷ ys)

-- As you can see, two lists are related by (ListR R) if
--   (i)  their lengths are equal
--   (ii) the elements in corresponding positions are related by R.

-- We will shortly make use of ListR, so you need to build some equipment.

{- ??? 3.27 Show that every list is pairwise equal to itself.
   (1 MARK)
-}

listR-refl : forall {X}(xs : List X) -> ListR _≡_ xs xs
listR-refl = {!!}

{- ??? 3.28 Build fmap for ListR, suitably "over" L.map.
   (1 MARK)
-}

ListR-map : ∀ {A B}                -- source element types
              {C D}                -- target element types
        (f : A -> C)(g : B -> D)   -- functions source to target
        {R : A -> B -> Set}        -- relation on source types
        {S : C -> D -> Set}        -- relation on target types
     -> (∀ {a b} → R a b -> S (f a) (g b))  -- source implies target
     -- Now, show why the target lists are related if the source lists are.
     -> ∀ {as bs} → ListR R as bs -> ListR S (L.map f as) (L.map g bs)
ListR-map = {!!}

END OF COMMENT eriskay -}

{- faray UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

-----------------------------------------------------
-- Cutting Things Up And Sticking Them Back Together
-----------------------------------------------------

-- This section is the heart of the exercise. It deals with the situation
-- where you have a structure that is subdivided in one way, but you need it
-- to be subdivided in another.

-- That's a situation which arises when you need to display multiple layers
-- of overlapping windows. The cutting structure of the front layer
-- determines which parts of the back layers you can see. So you will need
-- to *impose* the front structure onto the back layer, in order to extract
-- its visible parts.

module _ {I}(C : I <| I) where  -- we fix some notion of cutting

  -- A "Cutter" is a way of taking a *whole* thing and *choosing* how to cut
  -- it into the specified collection of *pieces*.

  Cutter : (I -> Set) -> Set
  Cutter P = {i : I}(c : Cuts C i)   -- given a size, choose how to cut
          -> P i                     -- and, given a whole P,
          -> All P (pieces C c)      -- get all the P pieces for your cut


{- ??? 3.29 For this concept to sink in, construct a NatCut cutter for
       vectors.
  (1 MARK) -}

-- HINT: It might help to think back to the good old days of
-- Coursework.One.

vecCutter : forall {X} -> Cutter NatCut (Vec X)
vecCutter = {!!}

module _ {I}(C : I <| I) where  -- we fix some notion of cutting

  -- Now, working in Tree NatCut, consider that we might have a structure
  -- which has a top level cut in one place:
  --
  --        <---tl---||--------tr-------->
  --
  -- But suppose we *wish* that it was cut differently, e.g., here:
  --
  --        <--------wl--------||---wr--->
  --
  -- If we are able to cut up the recursive substructures wherever we want,
  -- we can make our wish come true.
  --
  -- Project the cut we want onto the cut we've got. And cut there!
  --
  --        <--------wl--------||---wr--->
  --                           ||
  --                           vv
  --        <---tl---||--------tr-------->
  --        <---tl---|<--trl---||--trr-->>
  --
  -- That is, we leave the left piece alone and cut the right piece in two.
  -- In general, some pieces will be left alone; others will be cut.
  --
  -- We now have three pieces from which we can assemble the structure we
  -- need. How to do that?
  --
  -- Project the cut we've got onto the cut we want. And cut there!
  --
  --        <---tl---||--------tr-------->
  --                 ||
  --                 vv
  --        <--------wl--------||---wr--->
  --        <<--wll--||---wlr-->|---wr--->
  --
  -- In general, some pieces we want will be whole. Others will need to
  -- be assembled from multiple sub-pieces.
  --
  -- We now have the sizes we need. To finish the job, we just need the
  -- means to rearrange the pieces we've got into the structure we want.
  --
  --        <---tl---|<--trl---||--trr-->>
  --        <<--wll--||---wlr-->|---wr--->

  -- The following type captures the idea of being kept whole or cut further.

  SubCut : List I    -- a list of sub-piece sizes
        -> I         -- the size of the whole piece
        -> Set
  SubCut is i
    = (is ≡ (i ∷ []))  -- kept whole: there is one sub-piece,
                         -- with the same size as the piece
    ⊎ (Σ (Cuts C i) λ d → is ≡ pieces C d)  -- cut further
    -- ^^ there was a cut,  ^^ and the sub-pieces are that cut's pieces

  -- Now your turn. Hopefully this helps you get the idea.

  {- ??? 3.30 Assemble pieces from sub-pieces.
    (1 MARKS)
  -}

  glueSubCut : forall {P}
    -> {iss : List (List I)}       -- 2-layer list of sub-pieces you have
    -> {is : List I}               -- 1-layer list of pieces you want
    -> (ds : ListR SubCut iss is)  -- how sub-pieces relate to pieces
    -> All (All (Tree C P)) iss    -- now, given trees as sub-pieces,
    -> All (Tree C P) is           -- make the pieces!
  glueSubCut = {!!}

  -- What's the general recipe? Here goes.

  Recutter : Set
  Recutter =
    -- You get this information:
       {i : I}                         -- the size of the whole
    -> (c : Cuts C i)                  -- the cut we want
    -> (c' : Cuts C i)                 -- the cut we've been given
    -- You produce this information:
    -> Σ (List (List I)) λ iss  →        -- 2-layer list of wanted sub-pieces
       Σ (List (List I)) λ iss' →        -- 2-layer list of given sub-pieces
       ListR SubCut iss (pieces C c) ×   -- wanted sub-pieces fit wanted cut
       ListR SubCut iss' (pieces C c') × -- given sub-pieces fit given cut
       (∀ {P}                -- whatever the pieces are,
        -> All (All P) iss'  -- take the given sub-pieces and
        -> All (All P) iss)   -- deliver the wanted sub-pieces

  -- Now, let's work with stuff in Q for which we have a cutter,
  -- and suppose we possess a Recutter.

  module _ {Q}(cutQ : Cutter C Q)(recut : Recutter) where

    {- ??? 3.31 Build a Cutter for trees.
      (1 MARKS)
    -}

   -- HINTS:
    -- (i) Mutual recursion will probably be necessary; I've given you
    -- a gadget to cut pieces into sub-pieces to be mutually recursive
    -- with.
    -- (ii)  Each tree is either a leaf or a node made by some cut you don't want,
    --       but you have the equipment to deal with either situation.
    -- (iv)  "treeCutter" will also need "glueSubCut"

    treeCutter : Cutter C (Tree C Q)
    chopSubCut :
         {iss' : List (List I)}          -- sub-piece sizes
      -> {is' : List I}                  -- piece sizes
      -> (ds' : ListR SubCut iss' is')   -- how sub-pieces come from pieces
      -> All (Tree C Q) is'              -- now, given the pieces
      -> All (All (Tree C Q)) iss'       -- produce the sub-pieces

    treeCutter = {!!}

    chopSubCut [] [] = []
    chopSubCut (inj₁ refl ∷ ds') (t ∷ ts) = (t ∷ []) ∷ chopSubCut ds' ts
    chopSubCut (inj₂ (d' , refl) ∷ ds') (t ∷ ts) = treeCutter d' t ∷ chopSubCut ds' ts


    -- And, with that, we're ready to build the key device for working with
    -- overlays.


    {- ??? 3.32 Show that if you can combine a front *piece* with a back
           *tree*, then you can combine a front *tree* with a back *tree*.
      (1 MARK)
    -}

    -- HINT: treeIter and appAll are your friends here.

    overlay : ∀
         {P}  -- the type of pieces in the front layer
      --  Q, from module parameter above gives the type of pieces at the back
         {R}  -- the type of pieces in the combined output
      -> Π[        P ⇒ Tree C Q ⇒ Tree C R ]  -- front piece on back tree
      -> Π[ Tree C P ⇒ Tree C Q ⇒ Tree C R ]  -- front tree on back tree
    overlay = {!!}


-------------------------
-- Cutters for Matrices
-------------------------

-- A cutter for matrices is a special case of the general idea that
-- if we know how to cut in each dimension separately, we ought to be able
-- to cut multidimensional things, provided we have enough structure to
-- apply "inner" cuts through "outer" layers.
--
-- E.g., as a matrix is a column of rows, cutting vertically is cutting the
-- column, but cutting horizontally is cutting *all* the rows in the column.


{- ??? 3.32 Combine two dimensions of cutting.
   (2 MARKS)
-}

compCut :
  -- What's the general setup?
  ∀ {I J} → -- we have an I dimension and a J dimension
     (C : I <| I)(F : Set -> I -> Set)
     -- "inner" dimension with C-cuts corresponds to layers of F
  -> (D : J <| J)(G : Set -> J -> Set)
     -- "outer" dimension with D-cuts corresponds to layers of G
  -- What do we know about G?
  -> (∀ {X Y j} → (X -> Y) -> G X j -> G Y j)
     -- it has a suitable "map" operator
  -> (∀ {P : I -> Set}{is}{j} → G (All P is) j -> All (λ i → G (P i) j) is)
     -- you can "yank" All through it (i.e., it's "traversable")
  -- Now what's the deal? You get
  -> (∀ {X} → Cutter C (F X))  -- a polymorphic C-cutter for Fs
  -> (∀ {X} → Cutter D (G X))  -- a polymorphic D-cutter for Gs
  -- and you make a
  -> ∀ {X} → -- polymorphic
        Cutter (C |+| D) -- two-dimensional cutter
          λ { (i , j) -> G (F X i) j}  -- for Gs full of Fs.
compCut C F D G mapG yankG cf dg {i = i , j} cd gfx = {!!}


{- ??? 3.33 Show that you can "yank" through vectors, and thus acquire your
-- matrix cutter.
   (1 MARK)
-}

-- HINT: Time to bring out that All structure again!

vecYank : {P : ℕ -> Set} {is : List ℕ} {j : ℕ} ->
          Vec (All P is) j -> All (λ i → Vec (P i) j) is
vecYank = {!!}

matrixCutter : ∀ {X} → Cutter RectCut (Matrix X)
matrixCutter = compCut NatCut Vec NatCut Vec V.map vecYank vecCutter vecCutter


-------------------------
-- A Recutter for NatCut
-------------------------

-- In order to implement a recutter for NatCat, you will need to
-- analyse the situation where you have the *same* number, n, cut up
-- in two *different* ways, namely as (x + x') and as (y + y').

-- There are three possibilities:

-- x might be less than y (making x' greater than y')
--    <--------------------n------------------>
--    <-----x-----><------------x'------------>
--    <----------y--------><---------y'------->

-- x might be equal to y (making x' equal to y')
--    <--------------------n------------------>
--    <-----------x-----><---------x'--------->
--    <-----------y-----><---------y'--------->

-- x might be greater than y (making x' greater than y')
--    <--------------------n------------------>
--    <----------x--------><---------x'------->
--    <-----y-----><------------y'------------>

-- The following type presents all these possibilities:

data CutCompare (x x' y y' n : ℕ) : Set where
  cutLt : (d : ℕ) -> x + suc d ≡ y -> suc d + y' ≡ x' -> CutCompare x x' y y' n
  cutEq : x ≡ y -> x' ≡ y' -> CutCompare x x' y y' n
  cutGt : (d : ℕ) -> y + suc d ≡ x -> suc d + x' ≡ y' -> CutCompare x x' y y' n


{- ??? 3.34 Show that you can always compare two NatCuts in this sense.
   (2 MARKS)
-}

cutCompare : ∀ x x' y y' {n} -> x + x' ≡ n -> y + y' ≡ n -> CutCompare x x' y y' n
cutCompare = {!!}

{- ??? 3.35 Now use cutCompare to build yourself a natRecutter.
   (2 MARKS)
-}

natRecutter : Recutter NatCut
natRecutter = {!!}


-------------------------------------
-- Recutters in Multiple Dimensions
-------------------------------------

-- Now that you can recut lengths, it's time to show that you can
-- recut rectangles. In fact, if you can recut individual dimensions,
-- you can recut in any choice of dimensions.

module _                                -- You get:
    {I J}(C : I <| I)(D : J <| J)       -- notions of cut for two dimensions
    (rC : Recutter C)(rD : Recutter D)  -- recutters in both dimensions
  where

  {- ??? 3.36 Construct a recutter for the pair of dimensions, where each cut can
         be in either dimension.
     (4 MARKS)
  -}

-- Hints:
-- (i)   You will find you have four cases, two for each of the following
--       situations:
--       Either the cut wanted and the cut given are in the same dimension
--         (and you have a recutter for that dimension),
--       or the cut wanted and the cut given are in different dimensions,
--         (splitting the space into a kind of "matrix").
-- (ii)  The following "plumbing" operators might be useful to implement:
{-
plumb : ∀ {I J K}{P : K -> Set}{f : I -> J -> K}{js : I -> List J} ->
  Π[ All (All P) ∘′ L.map (λ i → L.map (f i) (js i)) ⇒
     All (λ i → All (P ∘′ f i) (js i)) ]

bmulp : ∀ {I J K}{P : K -> Set}{f : I -> J -> K}{js : I -> List J} ->
  Π[ All (λ i → All (P ∘′ f i) (js i)) ⇒
     All (All P) ∘′ L.map (λ i -> L.map (f i) (js i)) ]
-}
--       I would suggest to implement them using All-mapExt.

  recutPair : Recutter (C |+| D)
  recutPair = {!!}


-- After all that hard work, you obtain a recutter for RectCut!

rectRecutter : Recutter RectCut
rectRecutter = recutPair NatCut NatCut natRecutter natRecutter

END OF COMMENT faray -}

{- gigha UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
-- Building applications (15 MARKS in total)
------------------------------------------------------------------------------

-- We are almost ready to start managing windows!

-----------------------
-- Holes and Overlays
-----------------------

-- If S is some sort of "stuff", indexed by some sort of size, then
-- Holey S is the sized-indexed choice of "some stuff" or "a hole",
-- i.e., the absence of stuff. The point of a hole is to be
-- *transparent* in a display made of multiple layers. Holey is the
-- Maybe monad on (I -C> SET), but it's far too late in the process to
-- be distracted by that now.

data Holey {I : Set}(S : I -> Set)(i : I) : Set where
  hole  : Holey S i
  stuff : S i -> Holey S i


{- ??? 3.37 Show that if you can cut up "stuff", you can also cut up "holey stuff".
   (1 MARK)
-}

-- HINT: Another easy job for those who have done their All homework.

cutHoley : ∀ {I}(C : I <| I)(S : I -> Set) → Cutter C S -> Cutter C (Holey S)
cutHoley = {!!}

-- Now, we fix that we are working with rectangular stuff.

module OVERLAYING (S : ℕ × ℕ -> Set)(cS : Cutter RectCut S) where

  Background : ℕ × ℕ -> Set
  Background = Tree RectCut S       -- Backgrounds are made of stuff.

  Overlay : ℕ × ℕ -> Set
  Overlay = Tree RectCut (Holey S)  -- Overlays can also have holes.


  {- ??? 3.38 Show that you can cut overlays.
     (1 MARK)
  -}

  -- HINT: Specialise an operation you have already developed.

  overlayCutter : Cutter RectCut Overlay
  overlayCutter = {!!}


  {- ??? 3.39 Show that you can superimpose a "front" overlay on a
         "back" overlay, or completely fill in all the holes in an
         overlay, given a background.  In each case, the front overlay
         comes first, the back thing comes second, and the output is
         the combined thing.
     (1 MARK)
  -}

  -- HINT: Sounds like we want to overlay something, no?

  superimpose : Π[ Overlay ⇒ Overlay ⇒ Overlay ]
  superimpose = {!!}

  backstop : Π[ Overlay ⇒ Background ⇒ Background ]
  backstop = {!!}


----------------------------
-- Test Rig for Overlaying
----------------------------

-- You will need a correct implementation of both "RectCut" and "treeMatrix"
-- for this test to make sense.

-- With those in place, you should be able to judge your implementation of
-- "superimpose".

module OVERLAYEXAMPLE where

  data Solid {I : Set} : I -> Set where
    solid : Colour -> (i : I) -> Solid i

  cutSolid : Cutter RectCut Solid
  cutSolid c (solid x i) = pureAll (solid x) _

  seeHoleySolid : Π[ Holey Solid ⇒ Matrix Char ]
  seeHoleySolid (w , h) hole = replicate (replicate '.')
  seeHoleySolid (w , h) (stuff (solid x ._)) = replicate (replicate (art x)) where
    art : Colour -> Char
    art black   = '#'
    art red     = 'r'
    art green   = 'g'
    art yellow  = 'y'
    art blue    = 'b'
    art magenta = 'm'
    art cyan    = 'c'
    art white   = ' '

  open OVERLAYING Solid cutSolid

  frontExample backExample : Overlay (30 , 20)
  frontExample =
    < inj₂ (5 , 15 , refl)
    ,  leaf hole
    ∷ < inj₂ (10 , 5 , refl)
       ,  < inj₁ (5 , 25 , refl)
          ,  leaf hole
          ∷ < inj₁ (15 , 10 , refl)
             ,  leaf (stuff (solid red (15 , 10)))
             ∷ leaf hole
             ∷ [] >
          ∷ [] >
       ∷ leaf hole
       ∷ [] >
    ∷ [] >

  backExample =
    < inj₂ (7 , 13 , refl)
    ,  leaf hole
    ∷ < inj₂ (10 , 3 , refl)
       ,  < inj₁ (10 , 20 , refl)
          ,  leaf hole
          ∷ < inj₁ (15 , 5 , refl)
             ,  leaf (stuff (solid blue (15 , 10)))
             ∷ leaf hole
             ∷ [] >
          ∷ [] >
       ∷ leaf hole
       ∷ [] >
    ∷ [] >

  overlayExample : Overlay (30 , 20)
  overlayExample = superimpose _ frontExample backExample

  see : ∀ {wh} → Overlay wh -> List String
  see = showMatrix ∘′ treeMatrix seeHoleySolid _

module _ where
  open OVERLAYEXAMPLE

  seeFront seeBack seeOverlay : List String
  seeFront   = see frontExample
  seeBack    = see backExample
  seeOverlay = see overlayExample

  expectedSeeOverlay : List String
  expectedSeeOverlay =
    ".............................." ∷
    ".............................." ∷
    ".............................." ∷
    ".............................." ∷
    ".............................." ∷
    ".....rrrrrrrrrrrrrrr.........." ∷
    ".....rrrrrrrrrrrrrrr.........." ∷
    ".....rrrrrrrrrrrrrrrbbbbb....." ∷
    ".....rrrrrrrrrrrrrrrbbbbb....." ∷
    ".....rrrrrrrrrrrrrrrbbbbb....." ∷
    ".....rrrrrrrrrrrrrrrbbbbb....." ∷
    ".....rrrrrrrrrrrrrrrbbbbb....." ∷
    ".....rrrrrrrrrrrrrrrbbbbb....." ∷
    ".....rrrrrrrrrrrrrrrbbbbb....." ∷
    ".....rrrrrrrrrrrrrrrbbbbb....." ∷
    "..........bbbbbbbbbbbbbbb....." ∷
    "..........bbbbbbbbbbbbbbb....." ∷
    ".............................." ∷
    ".............................." ∷
    ".............................." ∷ []

  checkSeeOverlay : seeOverlay ≡ expectedSeeOverlay
  checkSeeOverlay = {!!}  -- this should be provable with refl

END OF COMMENT gigha -}

{- hunda UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

-----------------------------
-- Overlays for Applications
-----------------------------

open OVERLAYING (Matrix ColourChar) matrixCutter

-- For the rest of the exercise, we instantiate the "stuff" in an Overlay
-- to be matrices of coloured characters. That's exactly what we can display
-- in the terminal window.

-- An AppLayer refines the notion of display used in an application.
-- Instead of being a matrix of coloured characters, it is an Overlay,
-- which means it can have *holes*. Later, we'll look at how to superimpose
-- multiple layers.

AppLayer : ℕ × ℕ -> Set
AppLayer = Server AppInterface (Overlay ∩ CursorPosition)


{- ??? 3.40 Reconstruct the simple "rectApp" application as an
       AppLayer, generalising it to allow the colour to be chosen.
       Make it so that pressing ENTER cycles through all the colours.
   (2 MARKS)
-}

rectAppLayer : Colour -> Char -> Π[ AppLayer ]
rectAppLayer x c wh = {!!}


{- ??? 3.41 Show how to turn an AppLayer into an Application.
      (2 MARKS)
-}

-- Specification:
-- (i)   Any holes in the AppLayer should be filled with white spaces.
-- (ii)  The "stuff" in the AppLayer should display as it is given.
-- (iii) The Application should react as given by the AppLayer.

-- HINTS:
-- (iv)  Note that the type ensures that the Overlay is the size of the
--       screen.
-- (v)   You have already done the hard work by writing "treeMatrix" and
--       "backstop".

runAppLayer : Π[ AppLayer ⇒ Application ]
runAppLayer wh layer = {!!}

-- Congratulations, now you can go and run your fancy new main program
-- at the end of this file!


-----------------------------
-- Applications in a Window
-----------------------------

{- ??? 3.42 Write a function which takes an application of any size
       and displays it as a window at a given position in a screen of any
       size.
      (6 MARKS)
-}

-- Specification:
-- (i)   Any part of the screen not occupied by the application should
--       display as a hole.
-- (ii)  If the application does not fit entirely on the screen, you should
--       display the largest top-left corner of it that does fit.
-- (iii) Trap the arrow keys to move the window without resizing it.
-- (iv)  Trap the shifted arrow keys to resize the window without moving
--       its top left corner.

-- Hints:
-- (v)   You will need to compare positions and sizes in a way that generates
--       the evidence you need to inform cropping and padding. Consider
--       constructing a "view" which captures "less-or-equal" concretely:
--       Given two numbers, n and m,
--         either m is (n + d) for some d (so n is less than or equal to m),
--         or n is (m + suc d) for some d (so n is greater than m).
--       It may help to repackage the CutCompare "view".
-- (vi)  Padding amounts to filling parts of the screen with holes.
-- (vii) You should find overlayCutter useful.

windowLayer : ∀ (x y : ℕ)          -- left and top coordinates of window
              appWH                -- width and height of window application
           -> AppLayer appWH       -- the application to put in the window
           -> Π[ AppLayer ]         -- an application which fills the screen
windowLayer x y (aw , ah) layer (sw , sh) = {!!}

-- Congratulations, there is now another nwe main program for you to
-- try at the end of this file!


------------------------------------------------------------------------------
-- Layering Applications
------------------------------------------------------------------------------

{- ??? 3.43 Write a function which combines two layers into one.
      (2 MARKS)
-}

-- Specification:
-- (i)   The combined display should show the front display, except where it
--       has holes. You should make sure we can see through the holes in the
--       front to the display at the back, showing what's in those places.
-- (ii)  Trap the tab key, making it swap the front and back layers.
-- (iii) All other keystrokes should be handled by the front layer.

-- Hints:
-- (iv)  superimpose
-- (v)   How should "resize" events be handled? What do the types make you do?

twoLayers : Π[ AppLayer ⇒ AppLayer ⇒ AppLayer ]
--              ^^ front     ^^ back      ^^ combined
twoLayers wh front back = {!!}

-- You've reached the end, well done! Go and run your new main program
-- and relax. (How would you extend this program? What about more than
-- two layers, or creating layers on the fly, or displaying something
-- more interesting in the apps, or...?)

END OF COMMENT hunda -}


------------------------------------------------------------------------------
-- The Main Program
------------------------------------------------------------------------------

-- Here are a succession of different versions of the  main program to try
-- with the compiler. The first should be ready to run from the beginning.
-- The rest become gradually available as you complete more of the exercise.
-- Of course, you can only try one at a time, keeping the others commented
-- out.

main : IO ⊤
-- The following should work now.
main = appMain (rectApp '*')
-- when you have rectAppLayer working, try this
--main = appMain λ wh → runAppLayer wh (rectAppLayer green '*' _)
-- when you also have windowLayer working, try this
--main = appMain (λ wh → runAppLayer wh (windowLayer 2 2 (30 , 20) (rectAppLayer red '@' _) _))
-- when you have everything working, try this
--main = appMain (λ wh → runAppLayer wh (twoLayers wh (windowLayer 2 2 (30 , 20) (rectAppLayer magenta '!' _) wh) (windowLayer 12 4 (30 , 20) (rectAppLayer blue '.' _) wh)))

{-
To compile, move to your CS410 directory and invoke
  agda --compile --ghc-flag "-lncurses" Coursework/Three.agda

To run the program,
  ./Three

Ctrl-C quits the running application.
-}
