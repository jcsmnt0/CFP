open import Axioms
open import Structures.Category

module Functors.Const
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₃}
  {_⇒_ : O → O → Set ℓ₂} {_⇒′_ : O′ → O′ → Set ℓ₄}
  (cat : Category O _⇒_) (cat′ : Category O′ _⇒′_)
  where

open import Structures.Functor

open Category {{...}}

Δ : ∀ c → Functor cat cat′ (const c)
Δ _ = record
  { map = const id
  ; map-id = refl
  ; map-∘ = const (const (sym cancelLeft))
  }
