module Structures.InitialObject where

open import Axioms

open import Structures.Category
open import Structures.Functor
open import Structures.NaturalTransformation

open import Categories.SetCat
open import Functors.HomContrafunctor

record InitialObject
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (⊥ : O)
  :
  Set (ℓ₁ ⊔ ℓ₂) where

  open Category cat

  field
    initial : ∀ {x} → ⊥ ⇒ x
    uniqueness : ∀ {x} {m : ⊥ ⇒ x} → m ≡ initial

  ¬_ = ContraHomSet ⊥
