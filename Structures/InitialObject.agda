module Structures.InitialObject where

open import Axioms

open import Structures.Category

record InitialObject
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (⊥ : O)
  :
  Set (ℓ₁ ⊔ ℓ₂) where

  field
    initial : ∀ {x} → ⊥ ⇒ x
    uniqueness : ∀ {x} {m : ⊥ ⇒ x} → m ≡ initial
