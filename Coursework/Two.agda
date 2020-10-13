{-# OPTIONS --type-in-type #-}
------------------------------------------------------------------------
-- CS410 Advanced Functional Programming 2020
--
-- Coursework 2
------------------------------------------------------------------------

module Coursework.Two where

----------------------------------------------------------------------------
-- COURSEWORK 2 -- ISOMORPHIC DEFINITIONS, COMPILING A RAZOR, AND CATEGORICAL CONSTRUCTIONS
--
-- VALUE:     30% (divided over 60 marks, ie each mark is worth 0.5%)
-- DEADLINE:  3pm, Tuesday 3 November (Week 7)
--
-- SUBMISSION: Push your solutions to your own repo. Your last commit
-- before the deadline is your submitted version. However do get in
-- touch if you want to negotiate about extensions.
----------------------------------------------------------------------------

-- HINT: your tasks are labelled with the very searchable tag '???'

-- TIP: When you load this file, you will see lots of open goals. You
-- can focus on one at a time by using comments {- ... -} to switch
-- off the later parts of the file until you get there. Later on you
-- might want to switch off earlier parts to make loading later parts
-- faster (don't forget to switch them back on when you are done!).

open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_)
open import Data.Nat.Properties using (+-identityʳ; +-identityˡ; +-suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List as List using (List; []; _∷_; map)
open import Data.Vec  as Vec  using (Vec;  []; _∷_; map)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String hiding (show) renaming (_++_ to _<>_; replicate to repeat)
import Data.Nat.Show as NS using (show)
import Data.Bool.Show as BS using(show)
open import Function using (_∘′_; case_of_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; cong-app; sym; trans; module ≡-Reasoning; subst; isPropositional)
open import Relation.Nullary using (¬_)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)

open import Common.Category

------------------------------------------------------------------------
-- TIME FOR REFLECTION (10 MARKS in total)
------------------------------------------------------------------------

-- In this part, we are considering three different definitions of the
-- less-than relation on natural numbers. Two of them, `A._≤_` and
-- `B._≤_` we have already seen, whereas `C._≤_` is new. We want to
-- show that they are all *isomorphic*, in the following sense:

record _↔_ (A B : Set) : Set where
  field
    to         : A -> B
    from       : B -> A
    left-inverse-of : (x : A) -> from (to x) ≡ x
    right-inverse-of : (y : B) -> to (from y) ≡ y
open _↔_

infix 3 _↔_

-- (There is a similar definition in the standard library's
-- Function.Inverse, but that one is defined in more general terms,
-- and hence more inconvenient to use.)


------------------
module A where
------------------
  infix 4 _≤_

  -- Here is _≤_ defined by pattern matching:

  _≤_ : ℕ -> ℕ -> Set
  zero ≤ m = ⊤
  suc n ≤ zero = ⊥
  suc n ≤ suc m = n ≤ m

  {- ??? 2.1 Show that this definition is propositional, ie that any two
         proofs of it are equal.
     (1 MARK) -}

  propositional : (n m : ℕ) → isPropositional (n ≤ m)
  propositional n m p q = ?

------------------
module B where
------------------
  infix 4 _≤_

  -- Here is _≤_ defined inductively:

  data _≤_ : ℕ -> ℕ -> Set where
    z≤n : {n : ℕ} -> zero  ≤ n
    s≤s : {m n : ℕ} -> m ≤ n -> suc m ≤ suc n

  -- We already proved that this definition was propositional and
  -- transitive, so I'm not going to make you copy-paste the proofs.

  propositional : {n m : ℕ} -> isPropositional (n ≤ m)
  propositional z≤n z≤n = refl
  propositional (s≤s p) (s≤s q) = cong s≤s (propositional p q)

  transitive : ∀ {n m k} → n ≤ m -> m ≤ k -> n ≤ k
  transitive z≤n q = z≤n
  transitive (s≤s p) (s≤s q) = s≤s (transitive p q)

------------------
module C where
------------------
  infix 4 _≤_

  -- Here is a different inductive definition of _≤_. Your task now is
  -- to show that these are all "the same" definition. However you
  -- will see that they still behave different computationally!

  data _≤_ (m : ℕ) : ℕ → Set where
    ≤-refl : m ≤ m
    ≤-step : ∀ {n} → m ≤ n → m ≤ suc n

{- ??? 2.2 Show that you can translate back and forth between
       A.≤ and B.≤.
   (1 MARKS) -}

A→B : (n m : ℕ) -> n A.≤ m -> n B.≤ m
A→B = ?

B→A : {n m : ℕ} -> n B.≤ m -> n A.≤ m
B→A = ?

{- ??? 2.3 Now put together what you have so far to show that
       A.≤ and B.≤ are isomorphic.
   (1 MARK) -}

-- HINT: it is easy to prove equations in propositional types.

-- TIP: if you C-c C-c on an empty result, you get to do a definition
-- by "copattern matching", which is quite convenient: you give a
-- definition for each field in the record.

A↔B : (n m : ℕ) -> n A.≤ m ↔ n B.≤ m
A↔B n m = ?

{- ??? 2.4 Now show that you can translate between B.≤ and C.≤.
   (2 MARKS) -}


B→C : {n m : ℕ} -> n B.≤ m -> n C.≤ m
B→C = ?

C→B : {n m : ℕ} -> n C.≤ m -> n B.≤ m
C→B = ?

{- ??? 2.5 Use the above to get a cheap proof of transitivity
       for C.≤. (First try to do it by hand; it's not so easy!)
   (1 MARK) -}

C-transitive : ∀ {n m k} → n C.≤ m -> m C.≤ k -> n C.≤ k
C-transitive = ?

{- ??? 2.6 Now show that C.≤ is also propositional, and finish off the
       isomorphism between B.≤ and C.≲.
   (2 MARKS) -}

-- HINT: You might find the following lemma, and its lemma, useful:

¬sucn≤n : {n : ℕ} -> ¬ (suc  n C.≤ n)
¬sucn≤n {n} p = ? where
  peel : ∀ {n m} → suc n C.≤ suc m → n C.≤ m
  peel = ?

C-propositional : {n m : ℕ} → isPropositional (n C.≤ m)
C-propositional = ?

B↔C : (n m : ℕ) -> n B.≤ m ↔ n C.≤ m
B↔C n m = ?

{- ??? 2.7 Show that ↔ is transitive, and hence that A.≤ and C.≲ are
       isomorphic.
   (1 MARK) -}


↔-trans : {X Y Z : Set} -> X ↔ Y -> Y ↔ Z -> X ↔ Z
↔-trans p q = ?

A↔C : {n m : ℕ} -> n A.≤ m ↔ n C.≤ m
A↔C = ?

{- ??? 2.8 Finally, let's show that two randomly chosen large numbers
       are related by C.≤. For perspective, try to do it with C-c C-r
       first, then backtrack and use A↔C instead.
   (1 MARK) -}


myProof : 352 C.≤ 15231
myProof = ?

-- TERMINOLOGY: this proof method, where we swap between a definition
-- that reduces, and one which we can pattern match on, is usually
-- called "small-scale reflection". It has been involved in all (?)
-- efforts to prove substantial theorems succh as the Four Colour
-- Theorem and the Odd Order Theorem.



------------------------------------------------------------------------
-- EXTENDING AND COMPILING HUTTON'S RAZOR (25 MARKS in total)
------------------------------------------------------------------------

-- Here we explore the semantics of a small, but not-so-small-anymore
-- programming language. Compared with Hutton's usual Razor, we have
-- added Booleans with a comparision and if-then-else, and state in
-- the form of one memory cell, which we can read and write.

-----------------------
-- The untyped version
-----------------------

-- We start with an untyped version of the language.

module Untyped where

  data Expr : Set where
    num : ℕ -> Expr
    bit : Bool -> Expr
    get  : Expr
    put_then_ : Expr -> Expr -> Expr
    _+E_ : Expr -> Expr -> Expr
    _<E_ : Expr -> Expr -> Expr
    ifE_then_else_ : Expr -> Expr -> Expr -> Expr

  infix 4 _<E_
  infixl 5 _+E_
  infix 1 put_then_
  infix 2 ifE_then_else_

  -- Here are some example expressions:

  e1 : Expr
  e1 = num 4 +E num 5

  e2 : Expr
  e2 = put (num 7) then (get +E get)

  e3 : Expr
  e3 = put num 0 then (put num 7 then num 5) +E get

  e3' : Expr
  e3' = put num 0 then get +E (put num 7 then num 5)

  e4 : Expr
  e4 = put num 2 then ifE bit false then put num 1 then get else get

  e5 : Expr
  e5 = put num 7 then
         ifE get <E get +E num 1
           then ifE bit true then bit false else bit true
           else bit true

  -- Now let us explain how to evaluate such expressions. We will
  -- benefit from some hygiene, so let us define an evalutation monad
  -- to take care of the plumbing for us. We first define values:

  data Val : Set where
    num : ℕ -> Val
    bit : Bool -> Val

  -- Then we can define our monad. Unsurprisingly, it's a combination
  -- of the state monad `Store -> Store ×_` (for get and put) and the
  -- Maybe monad (for evaluation errors, eg type errors):

  Store = Val

  EvalM : Set -> Set
  EvalM A = Store -> (Store × Maybe A)

  {- ??? 2.9 Implement the monad operations return and bind. We can
         get away with not proving the laws, this time.
     (2 MARKS) -}

  return : {A : Set} -> A -> EvalM A
  return = ?

  _>>=_ : {A B : Set} -> EvalM A -> (A -> EvalM B) -> EvalM B
  (x >>= f) ρ = ?

  {- ??? 2.10 Now implement the specific operations that this monad
         supports: failing, getting and putting.
     (2 MARKS) -}

  fail : {A : Set} -> EvalM A
  fail = ?

  evalGet : EvalM Val
  evalGet = ?

  evalPut : EvalM Val -> EvalM Val -> EvalM Val
  evalPut = ?

  {- ??? 2.11 Use do-notation to implement evaluation.
     (3 MARKS) -}

  -- HINT: In a do-block, Agda let's you write
  --
  --   (c x) ← e where y → f y
  --
  -- to bind e and match it against the more precise pattern `c x`, using
  -- `f` if `e` didn't match `c x`

  eval : Expr -> EvalM Val
  eval = ?

  -- Here are some test cases you can comment in.  Let's only look at
  -- the produced value, and starting with 0 in the store.

  eval' : Expr -> Maybe Val
  eval' e = proj₂ (eval e (num 0))

  {-
  _ : eval' e1 ≡ just (num 9)
  _ = refl

  _ : eval' e2 ≡ just (num 14)
  _ = refl

  _ : eval' e3 ≡ just (num 12)
  _ = refl

  _ : eval' e3' ≡ just (num 5)
  _ = refl

  _ : eval' e4 ≡ just (num 2)
  _ = refl

  _ : eval' e5 ≡ just (bit false)
  _ = refl
  -}

  {- ??? 2.12 Prove the we can prove something about our language, by
         proving the following facts about put and get.
     (1 MARK) -}

  -- HINT: One should be really easy, if you've set up things right.

  getput : ∀ e ρ → eval (put get then e) ρ ≡ eval e ρ
  getput = ?

  putget : ∀ e ρ → proj₂ (eval (put e then get) ρ) ≡ proj₂ (eval e ρ)
  putget = ?

---------------------
-- The typed version
---------------------

-- Now let's look at a typed variant of the language. It's going to be
-- easier to work with, because we can get rid of the Maybe when
-- evaluating.

module Typed where

  -- We will have the smallest possible number of non-trivial types.

  data Ty : Set where
    nat : Ty
    bool  : Ty

  -- for simplicity, we assume the state contains a natural number (not a value)

  data Expr : Ty -> Set where
    num : ℕ -> Expr nat
    bit : Bool -> Expr bool
    get  : Expr nat
    put_then_  : ∀ {t} → Expr nat -> Expr t  -> Expr t
    _+E_ : Expr nat -> Expr nat -> Expr nat
    _<E_ : Expr nat -> Expr nat -> Expr bool
    ifE_then_else_ : ∀ {t} → Expr bool -> Expr t -> Expr t -> Expr t

  infix 4 _<E_
  infixl 5 _+E_
  infix 1 put_then_
  infix 2 ifE_then_else_

  -- Here are the example expressions again, but with types:

  e1 : Expr nat
  e1 = num 4 +E num 5

  e2 : Expr nat
  e2 = put (num 7) then (get +E get)

  e3 : Expr nat
  e3 = put num 0 then (put num 7 then num 5) +E get

  e3' : Expr nat
  e3' = put num 0 then get +E (put num 7 then num 5)

  e4 : Expr nat
  e4 = put num 2 then ifE bit false then put num 1 then get else get

  e5 : Expr bool
  e5 = put num 7 then
         ifE get <E get +E num 1
           then ifE bit true then bit false else bit true
           else bit true

  -- Here is our refined notion of evaluation monad. Note that it is
  -- no longer a monad from Set to Set!

  Val : Ty -> Set
  Val nat = ℕ
  Val bool = Bool

  Store = ℕ

  EvalM : (Ty -> Set) -> (Ty -> Set)
  EvalM A t = Store -> (Store × A t)

  {- ??? 2.13 Implement the monad operations for *this* EvalM.
     (2 MARKS) -}

  -- COMMENT: You might find this is already easier than before.

  return : ∀ {t} → Val t -> EvalM Val t
  return = ?

  _>>=_ : ∀ {t' t} → EvalM Val t -> (Val t -> EvalM Val t') -> EvalM Val t'
  (x >>= f) ρ = ?

  {- ??? 2.14 Now implement eval again in our glorious typed setting.
         Along the way, implement the get and put operations.
     (3 MARKS) -}

  evalGet : EvalM Val nat
  evalGet = ?

  evalPut : ∀ {t} → EvalM Val nat -> EvalM Val t -> EvalM Val t
  evalPut = ?

  eval : ∀ {t} → Expr t -> EvalM Val t
  eval = ?

  -- Note that we now always get a value! No more nothing

  eval₀ : ∀ {t} → Expr t -> ℕ -> Val t
  eval₀ e n = proj₂ (eval e n)

  -- We can also extract the final state, of course

  eval₁ : ∀ {t} → Expr t -> ℕ -> ℕ
  eval₁ e n = proj₁ (eval e n)

  -- For testing, here are the test cases from above again:

  eval' : ∀ {t} → Expr t -> Val t
  eval' e = eval₀ e 0

  {-
  _ : eval' e1 ≡ 9
  _ = refl

  _ : eval' e2 ≡ 14
  _ = refl

  _ : eval' e3 ≡ 12
  _ = refl

  _ : eval' e3' ≡ 5
  _ = refl

  _ : eval' e4 ≡ 2
  _ = refl

  _ : eval' e5 ≡ false
  _ = refl
  -}

-------------------
-- Compilation
-------------------

-- Let us now see how we can "compile" our language to a stack-based
-- machine. It's assembly code is given as follows, indexed by lists of
-- the types of the elements of the stack before and after execution:

  data Prog : (before : List Ty) -> (after : List Ty) -> Set where
    -- push to the stack
    PUSH : ∀ {ts t} → Val t → Prog ts (t ∷ ts)
    -- add top two elements of the stack
    ADD : ∀ {ts} → Prog (nat ∷ nat ∷ ts) (nat ∷ ts)
    -- compare top two elements of the stack
    CMP : ∀ {ts} → Prog (nat ∷ nat ∷ ts) (bool ∷ ts)
    -- load from memory to top of stack
    LOAD : ∀ {ts} → Prog ts (nat ∷ ts)
    -- save to memory to top of stack
    SAVE : ∀ {ts} → Prog (nat ∷ ts) ts
    -- conditionally choose a continuation based on top of stack
    BRANCH : ∀ {ts ts'} → Prog ts ts' -> Prog ts ts' -> Prog (bool ∷ ts) ts'
    -- sequential execution of programs
    _▹_ : ∀ {ts ts' ts''} → Prog ts ts' -> Prog ts' ts'' -> Prog ts ts''

  infixl 4 _▹_

  {- ??? 2.15 For future debugging but mostly for fun, write a show
         function for our assembly code. Every time you print a BRANCH, you
         should print "-" in front of each block, and then indent the entire
         block 2 spaces.
     (2 MARKS) -}

  -- EXAMPLE: the code corresponding to e5 above should be printed
  {-
     PUSH 7
     SAVE
     LOAD
     LOAD
     PUSH 1
     ADD
     CMP
     BRANCH
     - PUSH true
       BRANCH
       - PUSH false
       - PUSH true
     - PUSH true
  -}

  showIndent : ∀ {ts ts'} → ℕ -> Prog ts ts' -> String
  showIndent n c = ?

  show : ∀ {ts ts'} → Prog ts ts' -> String
  show = showIndent 0

  -- HINT: You can get Agda to print using your show function on a
  --       term by doing C-u C-u C-c C-n; easiest is to write a hole,
  --       eg
  --
  --         test = {!compile e5!}
  --
  --       and then do C-u C-u C-c C-n in the hole.

  {- ??? 2.16 Now show how to compile expressions into programs.
     (2 MARKS) -}

  -- HINT: You will get some help already by the types of the stack
  --       entries, but the real confidence that you have done the
  --       right thing comes later in this file in the form of the run
  --       function, and its soundness theorem.


  compile : ∀ {t ts} → Expr t -> Prog ts (t ∷ ts)
  compile = ?

  -- Let us now explain how to actually run our machine code. First we
  -- define what a type-respecting stack is, and hence what a machine
  -- configuration is.

  data Stack :  List Ty -> Set where
    [] : Stack []
    _∷_ : ∀ {ts t} → Val t -> Stack ts -> Stack (t ∷ ts)

  infixr 5 _∷_

  record Conf (ts : List Ty) : Set where
    constructor ⟨_,_⟩
    field
      stack : Stack ts
      memory : ℕ
  open Conf

  {- ??? 2.17 Implement the run function for our programs. Running a
  compiled expression should be the same as evaluating it.
     (3 MARKS) -}

  -- COMMENT: See how conveniently the types make sure that we always
  -- have enough things on the stack?

  run : ∀ {ts ts'} → Prog ts ts' → Conf ts -> Conf ts'
  run = ?

  {- ??? 2.18 In fact, *prove* that running a
         compiled expression is the same as evaluating it!
     (5 MARKS) -}

  -- HINT: most cases are straightforward, but if-then-else probably
  -- requires a lemma or two.


  open ≡-Reasoning

  soundness : ∀ {t ts ρ}{xs : Stack ts} → (e : Expr t) ->
              run (compile e) ⟨ xs , ρ ⟩ ≡ ⟨ eval₀ e ρ ∷ xs , eval₁ e ρ ⟩
  soundness = ?

-- NOTE: It is also possible to index programs by their meaning as
--       configuration transformers, and then observe that `compile` is
--       sound in the above sense by construction. It's a bit fiddly to do
--       this with `get` and `put` in the object language though, so we'd
--       better leave this for another time.


------------------------------------------------------------------------
-- FAMILIAR AND UNFAMILIAR CATEGORICAL CONSTRUCTIONS  (25 MARKS in total)
------------------------------------------------------------------------

-- NOTE: You have access to `ext` from Common.Category, as well as
-- a way to show natural transformations equal.

------------------------
-- Vectors as a functor
------------------------


-- We work with anonymous modules, so that we do not pollute the namespace
module _ where

  open Category
  open Functor

  {- ??? 2.19 Show that the preorder (ℕ, ≤) forms a category (like all
         preorders)
     (1 MARK) -}

  ℕ-as-cat : Category
  Obj ℕ-as-cat = ℕ
  Hom ℕ-as-cat = B._≤_ -- or change this to your favourite variant
  Category.id ℕ-as-cat = ?
  comp ℕ-as-cat = ?
  assoc ℕ-as-cat = ?
  identityˡ ℕ-as-cat = ?
  identityʳ ℕ-as-cat = ?

{- ??? 2.20 Show that if C is a category, then so is op C, which has
       the same objects as C, but the direction of all morphisms
       reversed.
   (1 MARK) -}

module _ (C : Category) where
  open Category C

  op : Category
  op = ?

module _ where

  open Category
  open Functor

{- ??? 2.21 Show that Vec X is a functor (ℕ, ≤) → SET.
   (1 MARK) -}

  restrict : {X : Set}{n m : ℕ} -> n B.≤ m -> Vec X m -> Vec X n
  restrict = ?

  VecX-functor : (X : Set) → Functor (op ℕ-as-cat) SET
  act (VecX-functor X) = Vec X
  fmap (VecX-functor X) = restrict
  identity (VecX-functor X) = ?
  homomorphism (VecX-functor X) = ?

module _ (C D : Category) where

  open Category
  open Functor
  open NaturalTransformation

  module CC = Category C
  module D = Category D

  {- ??? 2.22 Construct a category where the objects are functors from
         C to D, and the morphisms are natural transformations.
     (2 MARKS) -}

  FunctorCat : Category
  Obj FunctorCat = Functor C D
  Hom FunctorCat G H = NaturalTransformation G H
  id FunctorCat = ?
  comp FunctorCat {A = F} {G} {H} ρ η = ?
  assoc FunctorCat = ?
  identityˡ FunctorCat = ?
  identityʳ FunctorCat = ?

module _ where

  open Category
  open Functor
  open NaturalTransformation

  {- ??? 2.23 Show that actually Vec is a functor SET → ((ℕ, ≤) → SET).
     (2 MARKS) -}

  Vec-functor : Functor SET (FunctorCat (op ℕ-as-cat) SET)
  Vec-functor = ?

---------------------------
-- Families, categorically
---------------------------

-- The following is a generalisation of ↔ above from the category SET
-- to arbitrary categories. It is often the "right" notion if equality
-- of objects in a category.

record _≅_ {C : Category}(A B : Category.Obj C) : Set where
  open Category C
  field
    to         : A ⇒ B
    from       : B ⇒ A
    left-inverse-of : from ∘ to ≡ id
    right-inverse-of : to ∘ from ≡ id
open _≅_

infix 3 _≅_

-- We will consider a specific category, which on the one hand has a
-- concrete description, but on the other hand has an abstract
-- characterisation as the canonical way to add so-called coproducts
-- to a category. This is the category of families of objects of a
-- given category C.

open Category
open Functor
open NaturalTransformation

-- This is what it means to be a family of objects of C: you choose
-- an index set, and then a function from this set into the objects.

record Family (C : Category) : Set where
  constructor _,_
  field
    index : Set
    family : index -> Obj C
open Family

-- And this is the natural notion of morphism between such families:
-- a function `f` between index sets, and a transformation between
-- the objects of the families, using `f` to make the "types" match.

record Family-morphism (C : Category) (A B : Family C) : Set where
  constructor _,_
  field
    index-morphism : index A -> index B
    family-morphism : (x : index A) ->
                        Hom C (family A x) (family B (index-morphism x))
open Family-morphism

{- ??? 2.24 Show that if C is a category, then so is Fam C.
   (2 MARKS) -}

-- NOTE: Actually Fam is a functor CAT → CAT, but we won't need this
-- fact here.

Fam : Category -> Category
Obj (Fam C) = Family C
Hom (Fam C) = Family-morphism C
id (Fam C) = ?
comp (Fam C) {A , B} {A' , B'} {A'' , B''} (f' , g') (f , g) = ?
assoc (Fam C) {A , B} {A' , B'} {A'' , B''} {A''' , B'''}  {f , g} {f' , g'} {f'' , g''} = ?
identityˡ (Fam C) {A , B} {A' , B'} {f , g} = ?
identityʳ (Fam C) {A , B} {A' , B'} {f , g} = ?

-- Now, the claim is that Fam C is the set-indexed coproduct
-- completion of C. This means that Fam C has set-indexed coproducts
-- (we'll get to what this is in a second), that C embeds (full and
-- faithfully) into Fam C, and that any functor C → D where D has
-- set-indexed coproducts factors uniquely (up to isomorphism) through
-- Fam C. We will prove all but the last of these facts.

-- But first: coproducts. I'll explain the binary case, but Fam C has
-- A-indexed coproducts for any set A, not just for A = 2. Let X and Y
-- be objects in a category C. Their coproduct, if it exists, is
-- denoted X + Y, and comes with the following data:
--
-- * injections inl : X -> X + Y and inr : Y -> X + Y
--
-- * for any Q with f : X -> Q and g : Y -> Q, a unique mediating map
--   [ f , g ] : X + Y -> Q such that [ f , g ] ∘ inl = f and [ f , g ] ∘ inr = g.

{- ??? 2.25 Show that if Fam C always has A-indexed coproducts, for any set A.
       First, define the coproduct object, and the injections.
   (1 MARKS) -}


Coprod : {C : Category} -> (A : Set) -> (A -> Obj (Fam C)) -> Obj (Fam C)
Coprod A F = ?

inject : ∀ {C A F} → (a : A) -> Hom (Fam C) (F a) (Coprod A F)
inject {C} a = ?

{- ??? 2.26 Next, given a "competitor" coproduct (Q, f), define the mediating morphism.
   (1 MARKS) -}

-- This is the type of any mediator for a given competitor
Mediator : ∀ {C A} F Q -> ((a : A) -> Hom (Fam C) (F a) Q) -> Set
Mediator {C} {A} F Q f = Σ[ [f] ∈ (Hom (Fam C) (Coprod A F) Q) ] ((a : A) -> comp (Fam C) (inject a) [f] ≡ f a)

mediate : ∀ {C A F Q} -> (f : (a : A) -> Hom (Fam C) (F a) Q) -> Mediator F Q f
mediate {C} f = ?

{- ??? 2.27 In preparation for proving that the mediating morphism is
       unique, prove the following quite technical lemmas about when
       mediators and family morphisms are equal. For family morphisms,
       first fill in the data.
   (3 MARKS) -}

{- 1 mark eqMediator, 1 mark eqFamily-Morphism data, 1 mark eqFamily-Morphism + inverse itself -}

eqMediator : ∀ {C A F Q f} -> (m m' : Mediator {C} {A} F Q f) ->
             let (h , p) = m in let (h' , p') = m' in
             h ≡ h' -> m ≡ m'
eqMediator = ?

eqFamily-Morphism : ∀ {C A B} → (f g : Family-morphism C A B) ->
                    (p : {! SOMETHING GOES HERE !}) ->
                    {! AND SOMETHING GOES HERE !} ->
                    f ≡ g
eqFamily-Morphism f g p q = ?

eqFamily-Morphism⁻¹ : ∀ {C A B} → (f g : Family-morphism C A B) -> f ≡ g ->
                      Σ[ p ∈ ({! SOMETHING GOES HERE !}) ] ({! AND SOMETHING GOES HERE !})
eqFamily-Morphism⁻¹ f g pq = ?

{- ??? 2.28 Now you have what you need to prove the uniqueness of the mediating morphism; do it!
   (1 MARKS) -}


mediate-unique : ∀ {C A F Q} -> (f : (a : A) -> Hom (Fam C) (F a) Q) -> (h : Mediator F Q f) -> h ≡ mediate f
mediate-unique {C} {A} {F} {Q} f (h , p) = ?

{- ??? 2.29 Show that C embeds into Fam C, and that this embedding is
       so-called full and faithful: morphisms in the image of the
       embedding are determined by morphisms from C.
   (2 MARKS) -}


Embed : {C : Category} -> Functor C (Fam C)
Embed = ?

Embed-full : {C : Category} -> {X Y : Obj C}(h : Hom (Fam C) (act Embed X) (act Embed Y)) -> Σ[ f ∈ Hom C X Y ] (fmap Embed f ≡ h)
Embed-full = ?

Embed-faithful : {C : Category} -> {X Y : Obj C}{f g : Hom C X Y} -> fmap {C} Embed f ≡ fmap Embed g -> f ≡ g
Embed-faithful = ?

-------------------------
-- *Product* completions
-------------------------

-- Products A × B are the dual concept of coproducts: they come with
-- projections B ← A × B -> A, and if there is any other Q with
-- B ← Q -> A, then there is a unique morphism from Q *into* A × B.

-- Let's now get repaid for our toil by constructing the product
-- completion of a given category C, by the magic of duality, almost
-- for free.

{- ??? 2.30 Using only `Fam` and `op`, define the product completion
of C, so that the below commented out definitions make sense. Comment
them in when they do.
   (2 MARKS) -}

ProductCompletion : Category -> Category
ProductCompletion C = ?

{- -- comment me in
Prod : {C : Category} -> (A : Set) -> (A -> Obj (ProductCompletion C)) -> Obj (ProductCompletion C)
Prod = Coprod

project : ∀ {C A F} → (a : A) -> Hom (ProductCompletion C) (Prod A F) (F a)
project = inject

ProdMediator : ∀ {C A} F Q -> ((a : A) -> Hom (ProductCompletion C) Q (F a)) -> Set
ProdMediator = Mediator

prodMediate : ∀ {C A F Q} -> (f : (a : A) -> Hom (ProductCompletion C) Q (F a)) -> ProdMediator F Q f
prodMediate = mediate

prodMediate-unique : ∀ {C A F Q} -> (f : (a : A) -> Hom (ProductCompletion C) Q (F a)) -> (h : ProdMediator F Q f) -> h ≡ prodMediate f
prodMediate-unique = mediate-unique
-}

--------------------
-- The Pow Fam flip
--------------------

-- For Fam SET, there is yet another concrete description, based on
-- the following two equivalent way to describe a subset of a given
-- set X: either as a function X → Set, seen as a "membership"
-- predicate for the subset, or as the image of a function Y → X for
-- some Y. The latter gives rised to the so-called arrow category of
-- SET.

{- ??? 2.31 Show that SET^→ is a category.
   (1 MARK) -}

-- REMARK: C^→ makes sense for any category C, but life is a bit easier
-- for us if we just stick to SET^→.

SET^→ : Category
Obj SET^→ = Σ[ A ∈ Set ] Σ[ B ∈ Set ] (A -> B)
Hom SET^→ (A , B , f) (A' , B' , f') = Σ[ α ∈ (A -> A') ] Σ[ β ∈ (B → B') ] (β ∘′ f ≡ f' ∘′ α)
id SET^→ {A , B , f} = ?
comp SET^→ {A , B , f} {A' , B' , f'} {A'' , B'' , f''} (α , β , p) (α' , β' , p') = ?
assoc SET^→  = ?
identityˡ SET^→ = ?
identityʳ SET^→ = ?

-- Using the sledgehammer of uniqueness of identity proofs, we can
-- show that it's enough for the first two components of morphisms in
-- SET^→ to be equal for the whole morphisms to be equal.

eqMorphismSET^→ : {A B : Obj SET^→} -> {f g : Hom SET^→ A B} ->
                  let (α , β , p) = f in let (α' , β' , p') = g in
                  α ≡ α' -> β ≡ β' -> f ≡ g
eqMorphismSET^→ refl refl = cong (_ ,_) (cong (_ ,_) (uip _ _))

{- ??? 2.31 Now show that Fam SET and SET^→ are equivalent: construct
       functors in both directions and show that their compositions
       are isomorphic to the identity functor.
   (5 MARKS) -}


To : Functor (Fam SET) SET^→
To = ?

From : Functor SET^→ (Fam SET)
From = ?

Left-Inverse-Of : (X : Obj (Fam SET)) -> _≅_ {C = Fam SET} (act From (act To X)) X
Left-Inverse-Of = ?

Right-Inverse-Of : (Y : Obj SET^→) -> _≅_ {C = SET^→} (act To (act From Y)) Y
Right-Inverse-Of = ?

-- TIP: if using eqMorphismSET^→ in this construction, you might
-- have to specify the last component of the object B (by
-- "eqMorphismSET^→ {B = (_ , _ , ?)}", since this is not inferrable
-- by Agda
