open import Data.Product using (_,_)

open import Axioms

open import Structures.Category
open import Structures.Functor
open import Structures.Limit

open Category {{...}}

module Structures.Equalizer
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  {a b : O}
  (cat : Category O _⇒_)
  (f g : a ⇒ b)
  where

data I : Set where aᴵ bᴵ : I

data _⇒ᴵ_ : I → I → Set where
  idᴵ : ∀ {a} → a ⇒ᴵ a
  fᴵ gᴵ : aᴵ ⇒ᴵ bᴵ

_∘ᴵ_ : ∀ {a b c} → (b ⇒ᴵ c) → (a ⇒ᴵ b) → (a ⇒ᴵ c)
idᴵ ∘ᴵ idᴵ = idᴵ
idᴵ ∘ᴵ fᴵ = fᴵ
idᴵ ∘ᴵ gᴵ = gᴵ
fᴵ ∘ᴵ idᴵ = fᴵ
gᴵ ∘ᴵ idᴵ = gᴵ

cancelLeftᴵ : ∀ {a b} {f : a ⇒ᴵ b} → idᴵ ∘ᴵ f ≡ f
cancelLeftᴵ {f = idᴵ} = refl
cancelLeftᴵ {f = fᴵ} = refl
cancelLeftᴵ {f = gᴵ} = refl

cancelRightᴵ : ∀ {a b} {f : a ⇒ᴵ b} → f ∘ᴵ idᴵ ≡ f
cancelRightᴵ {f = idᴵ} = refl
cancelRightᴵ {f = fᴵ} = refl
cancelRightᴵ {f = gᴵ} = refl

assocᴵ : ∀ {a b c d} (h : c ⇒ᴵ d) (g : b ⇒ᴵ c) (f : a ⇒ᴵ b) → h ∘ᴵ (g ∘ᴵ f) ≡ (h ∘ᴵ g) ∘ᴵ f
assocᴵ idᴵ idᴵ idᴵ = refl
assocᴵ idᴵ idᴵ fᴵ = refl
assocᴵ idᴵ idᴵ gᴵ = refl
assocᴵ idᴵ fᴵ idᴵ = refl
assocᴵ idᴵ gᴵ idᴵ = refl
assocᴵ fᴵ idᴵ idᴵ = refl
assocᴵ gᴵ idᴵ idᴵ = refl

instance
  catᴵ : Category I _⇒ᴵ_
  catᴵ = record
    { _∘_ = _∘ᴵ_
    ; id = idᴵ
    ; assoc = assocᴵ
    ; cancelLeft = cancelLeftᴵ
    ; cancelRight = cancelRightᴵ
    }

D : I → O
D aᴵ = a
D bᴵ = b

instance
  functorD : Functor catᴵ cat D
  functorD = record
    { map = λ
      { {aᴵ} idᴵ → id
      ; {bᴵ} idᴵ → id
      ; fᴵ → f
      ; gᴵ → g
      }
    ; map-id = λ
      { {aᴵ} → refl
      ; {bᴵ} → refl
      }
    ; map-∘ = λ
      { {aᴵ} idᴵ idᴵ → sym cancelRight
      ; {aᴵ} idᴵ fᴵ → sym cancelRight
      ; {aᴵ} idᴵ gᴵ → sym cancelRight
      ; {bᴵ} idᴵ idᴵ → sym cancelRight
      ; fᴵ idᴵ → sym cancelLeft
      ; gᴵ idᴵ → sym cancelLeft
      }
    }

Equalizer : O → Set (ℓ₁ ⊔ ℓ₂)
Equalizer = Limit functorD
