open import Axioms

module Functors.Lift (ℓ ℓ′ : Level) where

open import Structures.Category
open import Structures.Functor

open import Categories.SetCat ℓ
open import Categories.SetCat (ℓ ⊔ ℓ′) renaming (setCategory to setCategory′)

liftFunctor : Functor setCategory setCategory′ (Lift {ℓ} {ℓ′})
liftFunctor = record
  { map = λ f x → lift (f (lower x))
  ; map-id = ext λ _ → refl
  ; map-∘ = λ f g → ext λ _ → refl
  }
