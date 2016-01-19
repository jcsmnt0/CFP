module Structures.Coproduct where

open import Axioms

open import Structures.Category

record Coproduct
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (a b c : O)
  :
  Set (ℓ₁ ⊔ ℓ₂) where

  field
    left : a ⇒ c
    right : b ⇒ c
