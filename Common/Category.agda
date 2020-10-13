{-# OPTIONS --type-in-type #-}
module Common.Category where

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK
import Function as Fun


postulate
  ext : Extensionality _ _


record Category : Set where
  eta-equality
  infixr 9 _∘_

  field
    Obj : Set
    Hom : Obj -> Obj -> Set

  _⇒_ = Hom

  field
    id  : ∀ {A} → (A ⇒ A)
    comp : ∀ {A B C} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)

  _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
  f ∘ g = comp g f

  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C}{h : C ⇒ D} →
                (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f

open Category

record Functor (C D : Category) : Set where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {A B} (f : A C.⇒ B) → act A D.⇒ act B

  field -- laws
    identity     : ∀ {A} → fmap (C.id {A}) ≡ D.id
    homomorphism : ∀ {X Y Z} {f : X C.⇒ Y}{g : Y C.⇒ Z} →
                   fmap (g C.∘ f) ≡ fmap g D.∘ fmap f
open Functor

record NaturalTransformation {C D : Category}
                             (F G : Functor C D) : Set where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D

  field
    transform   : ∀ X → F.act X D.⇒ G.act X
    natural     : ∀ X Y (f : X C.⇒ Y ) →
                  transform Y D.∘ F.fmap f ≡ G.fmap f D.∘ transform X
open NaturalTransformation

eqNatTrans : {C D : Category}{F G : Functor C D} ->
             (η ρ : NaturalTransformation F G) ->
             ((X : Obj C) -> transform η X ≡ transform ρ X) ->
             η ≡ ρ
eqNatTrans {C} η ρ p with ext p
... | refl = eqNatTrans' η ρ refl (ext λ X → ext λ Y → ext λ f → uip _ _) where
  eqNatTrans' : {C D : Category}{F G : Functor C D} ->
                (η ρ : NaturalTransformation F G) ->
                (p : transform η ≡ transform ρ) ->
                subst (λ z → (X Y : Obj C)(f : Hom C X Y) → (D ∘ z Y) (fmap F f) ≡ (D ∘ fmap G f) (z X)) p (natural η) ≡ (natural ρ) ->
               η ≡ ρ
  eqNatTrans' η ρ refl refl = refl


-- Examples

SET : Category
Obj SET = Set
Hom SET A B = A -> B
id SET = Fun.id
comp SET f g = g Fun.∘′ f
assoc SET = refl
identityˡ SET = refl
identityʳ SET = refl

