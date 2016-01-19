module Categories.SetCat.Coproduct ℓ where

open import Data.Product
open import Data.Sum

open import Axioms

open import Categories.SetCat ℓ

open import Structures.Coproduct
open import Structures.UniversalCoproduct

instance
  ⊎-coproduct : ∀ {a b} → Coproduct setCategory a b (a ⊎ b)
  ⊎-coproduct = record
    { left = inj₁
    ; right = inj₂
    }

  ⊎-universalCoproduct : ∀ {a b} → UniversalCoproduct setCategory a b (a ⊎ b)
  ⊎-universalCoproduct = record
    { coproduct = ⊎-coproduct
    ; factor = λ i′ j′ → [ i′ , j′ ]′ , refl ,′ refl
    }
