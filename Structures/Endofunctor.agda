module Structures.Endofunctor where

open import Axioms
open import Structures.Category
open import Structures.Functor

Endofunctor : ∀
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (F : O → O)
  →
  Set (ℓ₁ ⊔ ℓ₂)
Endofunctor cat = Functor cat cat
