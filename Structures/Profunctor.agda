module Structures.Profunctor where

open import Axioms

open import Structures.Bifunctor
open import Structures.Category
open import Structures.Functor

open import Categories.SetCat

open Category {{...}}

Profunctor : ∀
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
  {Oᴸ : Set ℓ₁} {Oᴿ : Set ℓ₂}
  {_⇒ᴸ_ : Oᴸ → Oᴸ → Set ℓ₃} {_⇒ᴿ_ : Oᴿ → Oᴿ → Set ℓ₄}
  (catᴸ : Category Oᴸ _⇒ᴸ_) (catᴿ : Category Oᴿ _⇒ᴿ_)
  (F : Oᴸ → Oᴿ → Set ℓ₅)
  →
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ lsuc ℓ₅)
Profunctor {ℓ₅ = ℓ} catᴸ catᴿ F = Bifunctor (op {{catᴸ}}) catᴿ (setCategory ℓ) F
