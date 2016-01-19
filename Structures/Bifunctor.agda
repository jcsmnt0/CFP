module Structures.Bifunctor where

open import Axioms

open import Structures.Category
open import Structures.Functor

open Category {{...}}

open ≡-Reasoning

record Bifunctor
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
  {Oᴸ : Set ℓ₁} {Oᴿ : Set ℓ₂} {O′ : Set ℓ₃}
  {_⇒ᴸ_ : Oᴸ → Oᴸ → Set ℓ₄} {_⇒ᴿ_ : Oᴿ → Oᴿ → Set ℓ₅} {_⇒′_ : O′ → O′ → Set ℓ₆}
  (catᴸ : Category Oᴸ _⇒ᴸ_) (catᴿ : Category Oᴿ _⇒ᴿ_) (cat′ : Category O′ _⇒′_)
  (F : Oᴸ → Oᴿ → O′)
  :
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where

  field
    bimap : ∀ {a b c d} → (a ⇒ᴸ b) → (c ⇒ᴿ d) → (F a c ⇒′ F b d)
    bimap-id : {a : Oᴸ} {b : Oᴿ} → bimap (id {a = a}) (id {a = b}) ≡ id
    bimap-∘ : ∀
      {a b c x y z}
      (f : a ⇒ᴸ b) (g : b ⇒ᴸ c)
      (h : x ⇒ᴿ y) (i : y ⇒ᴿ z)
      →
      bimap (g ∘ f) (i ∘ h) ≡ bimap g i ∘ bimap f h

  functorᴸ : ∀ {b} → Functor catᴸ cat′ (λ a → F a b)
  functorᴸ = record
    { map = λ f → bimap f id
    ; map-id = bimap-id
    ; map-∘ = λ f g →
        begin
          bimap (g ∘ f) id
        ≡⟨ cong (bimap (g ∘ f)) (sym cancelLeft) ⟩
          bimap (g ∘ f) (id ∘ id)
        ≡⟨ bimap-∘ f g id id ⟩
          bimap g id ∘ bimap f id
        ∎
    }

  functorᴿ : ∀ {a} → Functor catᴿ cat′ (λ b → F a b)
  functorᴿ = record
    { map = λ f → bimap id f
    ; map-id = bimap-id
    ; map-∘ = λ f g →
        begin
          bimap id (g ∘ f)
        ≡⟨ cong (flip bimap (g ∘ f)) (sym cancelLeft) ⟩
          bimap (id ∘ id) (g ∘ f)
        ≡⟨ bimap-∘ id id f g ⟩
          bimap id g ∘ bimap id f
        ∎
    }
