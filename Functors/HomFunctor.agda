open import Axioms
open import Structures.Category

module Functors.HomFunctor
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (a : O)
  where

open import Categories.SetCat ℓ₂

open import Structures.Functor

open Category {{...}}

instance
  homFunctor : Functor cat setCategory (HomSet a)
  homFunctor = record
    { map = _∘_
    ; map-id = ext (λ _ → cancelLeft)
    ; map-∘ = λ _ _ → ext (λ _ → sym (assoc _ _ _))
    }
