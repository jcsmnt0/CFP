module Categories.SetCat.ReaderEndofunctor ℓ (a : Set ℓ) where

open import Axioms

open import Categories.SetCat ℓ

open import Structures.Endofunctor

instance
  ReaderEndofunctor : Endofunctor setCategory (λ b → (a ⇒ˢ b))
  ReaderEndofunctor = record
    { map = λ g f x → g (f x)
    ; map-id = refl
    ; map-∘ = λ _ _ → refl
    }
