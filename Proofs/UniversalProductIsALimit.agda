module Proofs.UniversalProductIsALimit where

open import Axioms

open import Structures.Category
open import Structures.Functor
open import Structures.Limit
open import Structures.Product
open import Structures.UniversalProduct

open Category {{...}}
open Functor {{...}}
open UniversalProduct {{...}}

open import Data.Product using (_,_)

data I : Set where aᴵ bᴵ : I

data _⇒ᴵ_ : I → I → Set where
  idᴵ : ∀ {a} → a ⇒ᴵ a

_∘ᴵ_ : ∀ {a b c} → (b ⇒ᴵ c) → (a ⇒ᴵ b) → (a ⇒ᴵ c)
idᴵ ∘ᴵ idᴵ = idᴵ

assocᴵ : ∀ {a b c d} (h : c ⇒ᴵ d) (g : b ⇒ᴵ c) (f : a ⇒ᴵ b) → h ∘ᴵ (g ∘ᴵ f) ≡ (h ∘ᴵ g) ∘ᴵ f
assocᴵ idᴵ idᴵ idᴵ = refl

cancelLeftᴵ : ∀ {a b} {f : a ⇒ᴵ b} → idᴵ ∘ᴵ f ≡ f
cancelLeftᴵ {f = idᴵ} = refl

cancelRightᴵ : ∀ {a b} {f : a ⇒ᴵ b} → f ∘ᴵ idᴵ ≡ f
cancelRightᴵ {f = idᴵ} = refl

instance
  categoryI : Category I _⇒ᴵ_
  categoryI = record
    { _∘_ = _∘ᴵ_
    ; id = idᴵ
    ; assoc = assocᴵ
    ; cancelLeft = cancelLeftᴵ
    ; cancelRight = cancelRightᴵ
    }

D : ∀ {ℓ} {O : Set ℓ} → O → O → I → O
D a _ aᴵ = a
D _ b bᴵ = b

functorD : ∀ {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (one two : O)
  →
  Functor categoryI cat (D one two)
functorD cat one two = record
  { map = λ
    { {aᴵ} idᴵ → id
    ; {bᴵ} idᴵ → id
    }
  ; map-id = λ
    { {aᴵ} → refl
    ; {bᴵ} → refl
    }
  ; map-∘ = λ
    { {aᴵ} idᴵ idᴵ → sym cancelLeft
    ; {bᴵ} idᴵ idᴵ → sym cancelLeft
    }
  }

fromUniversalProduct : ∀
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  {a b c : O}
  {cat : Category O _⇒_}
  (universalProduct : UniversalProduct cat a b c)
  →
  Limit (functorD cat a b) c
fromUniversalProduct {c = c} {cat = cat} universalProduct = record
  { cone = record
    { α = λ
      { {aᴵ} → fst
      ; {bᴵ} → snd
      }
    ; naturalTransformation = record
        { naturality = λ
          { {aᴵ} idᴵ → trans cancelRight (sym cancelLeft)
          ; {bᴵ} idᴵ → trans cancelRight (sym cancelLeft)
          }
        }
      }
  ; factor = λ β nt → let m , (p , q) = factor (β aᴵ) (β bᴵ) in m , λ { aᴵ → p ; bᴵ → q }
  }
