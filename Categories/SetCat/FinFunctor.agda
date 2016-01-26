open import Data.Nat

module Categories.SetCat.FinFunctor where

open import Data.Fin hiding (_≤_)
open import Relation.Binary

open import Axioms
open import Lemmas

open import Structures.Category
open import Structures.Functor
open import Structures.NaturalTransformation

open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans; isPreorder to ≤-isPreorder)

open import Categories.Preorder ≤-isPreorder ≤-uniqueness
open import Categories.SetCat lzero

open import Functors.HomFunctor preorderCategory

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

naturalityFin : ∀ {a b c} (q : b ≤ c) (p : suc a ≤ b) → fromℕ≤ (≤-trans p q) ≡ inject≤ (fromℕ≤ p) q 
naturalityFin (s≤s _) (s≤s z≤n) = refl
naturalityFin (s≤s (s≤s q)) (s≤s (s≤s p)) = cong suc (naturalityFin (s≤s q) (s≤s p))

fromℕ≤-NT : ∀ {n} → NaturalTransformation (homFunctor (suc n)) finFunctor (λ _ → fromℕ≤)
fromℕ≤-NT = record { naturality = λ p → ext λ q → naturalityFin p q }
