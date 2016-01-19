module Structures.Cone where

open import Axioms

open import Functors.Const

open import Structures.Category
open import Structures.Functor
open import Structures.NaturalTransformation

record Cone
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₂}
  {_⇒_ : O → O → Set ℓ₃} {_⇒′_ : O′ → O′ → Set ℓ₄}
  {cat : Category O _⇒_} {cat′ : Category O′ _⇒′_}
  {D : O′ → O}
  (functorD : Functor cat′ cat D)
  (apex : O)
  :
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where

  field
    α : ∀ a → const apex a ⇒ D a
    naturalTransformation : NaturalTransformation (Δ cat′ cat apex) functorD α

