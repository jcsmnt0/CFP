module Structures.Colimit where

open import Data.Product

open import Axioms

open import Structures.Category
open import Structures.Cocone public
open import Structures.Functor
open import Structures.NaturalTransformation

open import Functors.Const

open Category {{...}}
open Cocone {{...}}

record Colimit
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₂}
  {_⇒_ : O → O → Set ℓ₃} {_⇒′_ : O′ → O′ → Set ℓ₄}
  {cat : Category O _⇒_} {cat′ : Category O′ _⇒′_}
  {D : O → O′}
  (functorD : Functor cat cat′ D)
  (apex : O′)
  :
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where

  field
    cocone : Cocone functorD apex

    factor :
      {c : O′}
      (β : ∀ a → D a ⇒′ const c a)
      (nt : NaturalTransformation functorD (Δ cat cat′ c) β)
      (a : O)
      →
      Σ[ m ∈ apex ⇒′ c ] (∀ a → β a ≡ m ∘ α a)

  instance
    coconeCocone : Cocone functorD apex
    coconeCocone = cocone
