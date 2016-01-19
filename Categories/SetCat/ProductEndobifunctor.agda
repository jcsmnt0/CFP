module Categories.SetCat.ProductEndobifunctor ℓ where

open import Data.Product using (_×_; _,_)

open import Axioms

open import Categories.SetCat ℓ

open import Structures.Endobifunctor

instance
  ×-Endobifunctor : Endobifunctor setCategory _×_
  ×-Endobifunctor = record
    { bimap = λ { f g (x , y) → f x , g y }
    ; bimap-id = ext λ _ → refl
    ; bimap-∘ = λ _ _ _ _ → ext λ _ → refl
    }
