module Categories.SetCat.SumEndobifunctor ℓ where

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Axioms

open import Categories.SetCat ℓ

open import Structures.Endobifunctor

instance
  ×-Endobifunctor : Endobifunctor setCategory _⊎_
  ×-Endobifunctor = record
    { bimap = λ f g → λ { (inj₁ x) → inj₁ (f x); (inj₂ y) → inj₂ (g y) }
    ; bimap-id = ext λ { (inj₁ _) → refl; (inj₂ _) → refl }
    ; bimap-∘ = λ _ _ _ _ → ext λ { (inj₁ _) → refl; (inj₂ _) → refl }
    }
