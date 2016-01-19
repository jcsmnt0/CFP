module Categories.SetCat.InitialObject ℓ where

open import Axioms

open import Categories.SetCat ℓ

open import Structures.InitialObject

data ⊥ : Set ℓ where

instance
  ⊥-initial : InitialObject setCategory ⊥
  ⊥-initial = record
    { initial = λ ()
    ; uniqueness = ext λ ()
    }
