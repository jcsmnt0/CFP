open import Structures.Category

module Categories.Product
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {Oᴸ : Set ℓ₁} {Oᴿ : Set ℓ₂}
  {_⇒ᴸ_ : Oᴸ → Oᴸ → Set ℓ₃} {_⇒ᴿ_ : Oᴿ → Oᴿ → Set ℓ₄}
  (catᴸ : Category Oᴸ _⇒ᴸ_) (catᴿ : Category Oᴿ _⇒ᴿ_)
  where

open import Data.Product using (_×_; _,_)

open import Axioms

open Category {{...}}

Oˣ : Set (ℓ₁ ⊔ ℓ₂)
Oˣ = Oᴸ × Oᴿ

_⇒ˣ_ : Oˣ → Oˣ → Set (ℓ₃ ⊔ ℓ₄)
(aᴸ , aᴿ) ⇒ˣ (bᴸ , bᴿ) = (aᴸ ⇒ᴸ bᴸ) × (aᴿ ⇒ᴿ bᴿ)

instance
  productCategory : Category Oˣ _⇒ˣ_
  productCategory = record
    { _∘_ = λ { (gᴸ , gᴿ) (fᴸ , fᴿ) → (gᴸ ∘ fᴸ) , (gᴿ ∘ fᴿ) }
    ; id = id , id
    ; assoc = λ _ _ _ → cong₂ _,_ (assoc _ _ _) (assoc _ _ _)
    ; cancelLeft = cong₂ _,_ cancelLeft cancelLeft
    ; cancelRight = cong₂ _,_ cancelRight cancelRight
    }
