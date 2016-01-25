open import Data.Nat

module Functors.Fin where

open import Data.Fin hiding (_≤_)
open import Relation.Binary

open import Axioms
open import Lemmas

open import Structures.Category
open import Structures.Functor

open DecTotalOrder decTotalOrder using () renaming (isPreorder to ≤-isPreorder)

open import Categories.Preorder ≤-isPreorder ≤-uniqueness
open import Categories.SetCat lzero

open Category {{...}}

mapFin : ∀ {m n} → m ≤ n → Fin m → Fin n
mapFin p i = inject≤ i p

mapFin-id : ∀ {n} (i : Fin n) → mapFin id i ≡ id {{setCategory}} i
mapFin-id zero = refl
mapFin-id (suc i) = cong suc (mapFin-id i)

mapFin-∘ : ∀ {a b c} (f : a ≤ b) (g : b ≤ c) i → mapFin (g ∘ f) i ≡ (mapFin g ∘ mapFin f) i
mapFin-∘ (s≤s f) (s≤s g) zero = refl
mapFin-∘ (s≤s f) (s≤s g) (suc i) = cong suc (mapFin-∘ f g i)

instance
  finFunctor : Functor preorderCategory setCategory Fin
  finFunctor = record
    { map = λ p → mapFin p
    ; map-id = ext mapFin-id
    ; map-∘ = λ f g → ext (mapFin-∘ f g)
    }
