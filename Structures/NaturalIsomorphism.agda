module Structures.NaturalIsomorphism where

open import Axioms

open import Structures.Category
open import Structures.Functor
open import Structures.NaturalTransformation

open Category {{...}}

record NaturalIsomorphism
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₂}
  {_⇒_ : O → O → Set ℓ₃} {_⇒′_ : O′ → O′ → Set ℓ₄}
  {cat : Category O _⇒_} {cat′ : Category O′ _⇒′_}
  {F : O → O′} {G : O → O′}
  (functorF : Functor cat cat′ F) (functorG : Functor cat cat′ G)
  (α : ∀ a → F a ⇒′ G a)
  (β : ∀ a → G a ⇒′ F a)
  :
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where

  field
    rightNT : NaturalTransformation functorF functorG α
    leftNT : NaturalTransformation functorG functorF β
    leftId : ∀ x → α x ∘ β x ≡ id
    rightId : ∀ x → β x ∘ α x ≡ id
