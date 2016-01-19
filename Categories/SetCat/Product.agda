module Categories.SetCat.Product ℓ where

open import Data.Product

open import Axioms

open import Categories.SetCat ℓ

open import Structures.Product
open import Structures.UniversalProduct

instance
  ×-product : ∀ {a b} → Product setCategory a b (a × b)
  ×-product = record
    { fst = proj₁
    ; snd = proj₂
    }

instance
  ×-universalProduct : ∀ {a b} → UniversalProduct setCategory a b (a × b)
  ×-universalProduct = record
    { product = ×-product
    ; factor = λ p′ q′ → < p′ , q′ > , refl ,′ refl
    }
