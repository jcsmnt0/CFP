module Functors.Compose where

open import Axioms

open import Structures.Category
open import Structures.Functor

open Category {{...}}
open Functor {{...}}

_⊚_ : ∀
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
  {O : Set ℓ₁} {O′ : Set ℓ₂} {O“ : Set ℓ₃}
  {_⇒_ : O → O → Set ℓ₄} {_⇒′_ : O′ → O′ → Set ℓ₅} {_⇒“_ : O“ → O“ → Set ℓ₆}
  {cat : Category O _⇒_} {cat′ : Category O′ _⇒′_} {cat“ : Category O“ _⇒“_}
  {F : O → O′} {G : O′ → O“}
  (functorG : Functor cat′ cat“ G) (functorF : Functor cat cat′ F)
  →
  Functor cat cat“ (λ x → G (F x))
_⊚_ {cat = cat} {cat′ = cat′} {cat“ = cat“} functorF functorG = record
  { map = λ f → map (map f)
  ; map-id =
      begin
        map (map id)
      ≡⟨ cong map map-id ⟩
        map id
      ≡⟨ map-id ⟩
        id
      ∎
  ; map-∘ = λ f g →
      begin
        map (map (g ∘ f))
      ≡⟨ cong map (map-∘ f g) ⟩
        map (map g ∘ map f)
      ≡⟨ map-∘ (map f) (map g) ⟩
        map (map g) ∘ map (map f)
      ∎
  }
  
