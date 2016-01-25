module Categories.SetCat.ListEndofunctor ℓ where

open import Data.List
open import Function

open import Axioms

open import Categories.SetCat ℓ

open import Structures.Endofunctor

map-id : ∀ {a : Set ℓ} (x : List a) → map id x ≡ id x
map-id [] = refl
map-id (x ∷ xs) rewrite map-id xs = refl

map-∘ : ∀ {a b c} (f : a ⇒ˢ b) (g : b ⇒ˢ c) (x : List a) → map (g ∘ f) x ≡ (map g ∘ map f) x
map-∘ f g [] = refl
map-∘ f g (x ∷ xs) rewrite map-∘ f g xs = refl

instance
  ListEndofunctor : Endofunctor setCategory List
  ListEndofunctor = record
    { map = map
    ; map-id = ext map-id
    ; map-∘ = λ f g → ext (map-∘ f g)
    }
