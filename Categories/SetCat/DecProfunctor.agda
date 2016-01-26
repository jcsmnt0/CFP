module Categories.SetCat.DecProfunctor where

open import Data.Empty
open import Function
open import Relation.Nullary

open import Axioms

open import Structures.Bifunctor
open import Structures.Category
open import Structures.Profunctor

open import Categories.SetCat

data Dec² {ℓ} (a : Set ℓ) (b : Set ℓ) : Set ℓ where
  yes² : b → Dec² a b
  no² : ¬ a → Dec² a b

join : ∀ {ℓ} {a : Set ℓ} → Dec² a a → Dec a
join (yes² x) = yes x
join (no² ¬x) = no ¬x

split : ∀ {ℓ} {a : Set ℓ} → Dec a → Dec² a a
split (yes x) = yes² x
split (no ¬x) = no² ¬x

bimap : ∀ {ℓ} {a b c d : Set ℓ} → (b → a) → (c → d) → Dec² a c → Dec² b d
bimap f g (yes² x) = yes² (g x)
bimap f g (no² ¬x) = no² (¬x ∘ f)

bimap-id : ∀ {ℓ} {a b : Set ℓ} → bimap {a = a} {c = b} id id ≡ id
bimap-id = ext λ { (yes² _) → refl ; (no² _) → refl }

bimap-∘ : ∀
  {ℓ}
  {a b c x y z : Set ℓ}
  (f : b → a) (g : c → b)
  (h : x → y) (i : y → z)
  →
  bimap (f ∘ g) (i ∘ h) ≡ bimap g i ∘ bimap f h
bimap-∘ f g h i = ext λ { (yes² _) → refl ; (no² _) → refl }

dec²-Profunctor : ∀ {ℓ} → Profunctor (setCategory ℓ) (setCategory ℓ) Dec²
dec²-Profunctor = record
  { bimap = bimap
  ; bimap-id = bimap-id
  ; bimap-∘ = bimap-∘
  }
