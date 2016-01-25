open import Axioms
open import Structures.Category

module Functors.HomContrafunctor
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (a : O)
  where

open import Structures.Functor

open import Categories.SetCat ℓ₂

open import Functors.HomFunctor (Category.op cat) a

open Category cat

instance
  homContrafunctor : Contrafunctor cat setCategory (ContraHomSet a)
  homContrafunctor = homFunctor
