open import Axioms
open import Structures.Category
open import Structures.Functor

open Category {{...}}
open Functor {{...}}

module Structures.NaturalTransformation where

record NaturalTransformation
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₂}
  {_⇒_ : O → O → Set ℓ₃} {_⇒′_ : O′ → O′ → Set ℓ₄}
  {cat : Category O _⇒_} {cat′ : Category O′ _⇒′_}
  {F : O → O′} {G : O → O′}
  (functorF : Functor cat cat′ F) (functorG : Functor cat cat′ G)
  (α : ∀ a → F a ⇒′ G a)
  :
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where

  constructor NT

  field
    naturality : ∀ {a b} (f : a ⇒ b) → α b ∘ map f ≡ map f ∘ α a
