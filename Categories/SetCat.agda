module Categories.SetCat ℓ where

open import Axioms

open import Structures.Category

infixr 1 _⇒ˢ_
_⇒ˢ_ : Set ℓ → Set ℓ → Set ℓ
a ⇒ˢ b = a → b

instance
  setCategory : Category (Set ℓ) _⇒ˢ_
  setCategory = record
      { _∘_ = λ g f x → g (f x)
      ; id = λ x → x
      ; assoc = λ _ _ _ → ext λ _ → refl
      ; cancelLeft = ext λ _ → refl
      ; cancelRight = ext λ _ → refl
      }

