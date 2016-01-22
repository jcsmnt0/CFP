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

-- if all of functorF, functorG, and α in the types of the NTs are definitionally equal, the NTs themselves
-- are equal, because the only other component of a natural transformation is the evidence for the naturality
-- condition, and all functions returning equality proofs of the same type are equal given axiom K and
-- extensionality.
congNT : ∀
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {Oᵅ : Set ℓ₂}
  {_⇒_ : O → O → Set ℓ₃} {_⇒ᵅ_ : Oᵅ → Oᵅ → Set ℓ₄}
  {cat : Category O _⇒_} {catᵅ : Category Oᵅ _⇒ᵅ_}
  {F : O → Oᵅ} {G : O → Oᵅ}
  {functorF : Functor cat catᵅ F} {functorG : Functor cat catᵅ G}
  {α : ∀ a → F a ⇒ᵅ G a}
  {nt nt′ : NaturalTransformation functorF functorG α}
  →
  nt ≡ nt′
congNT = cong NT (ext-implicit λ _ → ext-implicit λ _ → ext λ _ → K)
