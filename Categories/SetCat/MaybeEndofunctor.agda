module Categories.SetCat.MaybeEndofunctor ℓ where

open import Data.Maybe
open import Function

open import Axioms

open import Categories.SetCat ℓ

open import Structures.Endofunctor

map-id : ∀ {a : Set ℓ} (x : Maybe a) → map id x ≡ id x
map-id (just x) = refl
map-id nothing = refl

map-∘ : ∀ {a b c} (f : a ⇒ˢ b) (g : b ⇒ˢ c) (x : Maybe a) → map (g ∘ f) x ≡ (map g ∘ map f) x
map-∘ f g (just x) = refl
map-∘ f g nothing = refl

instance
  MaybeEndofunctor : Endofunctor setCategory Maybe
  MaybeEndofunctor = record
    { map = map
    ; map-id = ext map-id
    ; map-∘ = λ f g → ext (map-∘ f g)
    }

