open import Structures.Category

module Structures.Pullback
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  {a b c : O}
  (f : a ⇒ b)
  (g : c ⇒ b)
  where

open import Data.Product using (_,_)

open import Axioms

open import Structures.Functor
open import Structures.Limit

open Category {{...}}

data I : Set where aᴵ bᴵ cᴵ : I

-- "this diagram is often called a span"
data _⇒ᴵ_ : I → I → Set where
  idᴵ : ∀ {x} → x ⇒ᴵ x
  fᴵ : aᴵ ⇒ᴵ bᴵ
  gᴵ : cᴵ ⇒ᴵ bᴵ

_∘ᴵ_ : ∀ {x y z} → (y ⇒ᴵ z) → (x ⇒ᴵ y) → (x ⇒ᴵ z)
h ∘ᴵ idᴵ = h
idᴵ ∘ᴵ h = h

instance
  catᴵ : Category I _⇒ᴵ_
  catᴵ = record
    { _∘_ = _∘ᴵ_
    ; id = idᴵ
    ; assoc = λ
        { {aᴵ} h g idᴵ → refl
        ; {bᴵ} h g idᴵ → refl
        ; {cᴵ} h g idᴵ → refl
        ; h idᴵ fᴵ → refl
        ; h idᴵ gᴵ → refl
        }
    ; cancelLeft = λ
        { {f = idᴵ} → refl
        ; {f = fᴵ} → refl
        ; {f = gᴵ} → refl
        }
    ; cancelRight = λ
        { {f = idᴵ} → refl
        ; {f = fᴵ} → refl
        ; {f = gᴵ} → refl
        }
    }

D : I → O
D aᴵ = a
D bᴵ = b
D cᴵ = c

instance
  functorD : Functor catᴵ cat D
  functorD = record
    { map = λ
        { {aᴵ} idᴵ → id
        ; {bᴵ} idᴵ → id
        ; {cᴵ} idᴵ → id
        ; fᴵ → f
        ; gᴵ → g
        }
    ; map-id = λ { {aᴵ} → refl ; {bᴵ} → refl ; {cᴵ} → refl }
    ; map-∘ = λ
        { {aᴵ} idᴵ idᴵ → sym cancelLeft
        ; {bᴵ} idᴵ idᴵ → sym cancelLeft
        ; {cᴵ} idᴵ idᴵ → sym cancelLeft
        ; idᴵ fᴵ → sym cancelRight
        ; idᴵ gᴵ → sym cancelRight
        ; fᴵ idᴵ → sym cancelLeft
        ; gᴵ idᴵ → sym cancelLeft
        }
    }

Pullback : O → Set (ℓ₁ ⊔ ℓ₂)
Pullback = Limit functorD
