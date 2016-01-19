module Structures.Endobifunctor where

open import Axioms

open import Structures.Bifunctor
open import Structures.Category

Endobifunctor : ∀
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (F : O → O → O)
  →
  Set (ℓ₁ ⊔ ℓ₂)
Endobifunctor cat = Bifunctor cat cat cat

