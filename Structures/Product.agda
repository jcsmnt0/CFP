module Structures.Product where

open import Axioms

open import Structures.Category

record Product
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (a b c : O)
  :
  Set (ℓ₁ ⊔ ℓ₂) where

  field
    fst : c ⇒ a
    snd : c ⇒ b
