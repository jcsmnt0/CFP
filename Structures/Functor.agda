module Structures.Functor where

open import Axioms

open import Structures.Category

record Functor
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₃}
  {_⇒_ : O → O → Set ℓ₂} {_⇒′_ : O′ → O′ → Set ℓ₄}
  (cat : Category O _⇒_) (cat′ : Category O′ _⇒′_) 
  (F : O → O′)
  :
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where

  open Category cat
  open Category cat′ renaming (id to id′; _∘_ to _∘′_)

  field
    map : ∀ {a b} → (a ⇒ b) → (F a ⇒′ F b)
    map-id : ∀ {a} → map (id {a}) ≡ id′
    map-∘ : ∀ {a b c} → (f : a ⇒ b) → (g : b ⇒ c) → map (g ∘ f) ≡ map g ∘′ map f

Contrafunctor : ∀
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₃}
  {_⇒_ : O → O → Set ℓ₂} {_⇒′_ : O′ → O′ → Set ℓ₄}
  (cat : Category O _⇒_) (cat′ : Category O′ _⇒′_) 
  (F : O → O′)
  →
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
Contrafunctor cat = Functor (Category.op cat)
