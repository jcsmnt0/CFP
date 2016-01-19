module Structures.Limit where

open import Data.Product

open import Axioms

open import Functors.Const

open import Structures.Category
open import Structures.Cone public
open import Structures.Functor
open import Structures.NaturalTransformation

open Category {{...}}
open Cone {{...}}

record Limit
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
    cone : Cone functorD apex

    factor :
      {c : O′}
      (β : ∀ a → const c a ⇒′ D a)
      (nt : NaturalTransformation (Δ cat cat′ c) functorD β)
      →
      Σ[ m ∈ c ⇒′ apex ] (∀ a → β a ≡ α a ∘ m)

  instance
    coneCone : Cone functorD apex
    coneCone = cone
