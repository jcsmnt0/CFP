module Structures.UniversalCoproduct where

open import Data.Product

open import Axioms

open import Structures.Category
open import Structures.Coproduct public

open Category {{...}}
open Coproduct {{...}} public

record UniversalCoproduct
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (a b c : O)
  :
  Set (ℓ₁ ⊔ ℓ₂) where

  field
    coproduct : Coproduct cat a b c
    factor : ∀ {c′} → (p : a ⇒ c′) → (q : b ⇒ c′) → Σ[ m ∈ c ⇒ c′ ] ((p ≡ m ∘ left) × (q ≡ m ∘ right))

  instance
    coproductCoproduct : Coproduct cat a b c
    coproductCoproduct = coproduct
