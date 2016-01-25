open import Data.Nat

module Categories.SetCat.VecEndofunctor ℓ (n : ℕ) where

open import Data.Fin hiding (lift)
open import Data.Vec using (Vec; []; _∷_; map)
open import Function using (id; _∘_)

open import Axioms
open import Functors.Representable

open import Categories.SetCat ℓ

open import Structures.Endofunctor

lookup : ∀ {ℓ m} {a : Set ℓ} → Fin m → Vec a m → a
lookup () []
lookup zero (x ∷ _) = x
lookup (suc i) (_ ∷ xs) = lookup i xs

tabulate : ∀ {ℓ m} {a : Set ℓ} → (Fin m → a) → Vec a m
tabulate {m = zero} _ = []
tabulate {m = suc m} f = f zero ∷ tabulate (f ∘ suc)

map-id : ∀ {ℓ m} {a : Set ℓ} (xs : Vec a m) → map id xs ≡ xs
map-id [] = refl
map-id (_ ∷ _) = cong (_∷_ _) (map-id _)

map-∘ : ∀ {ℓ m} {a b c : Set ℓ} (f : a → b) (g : b → c) (xs : Vec a m) → map (g ∘ f) xs ≡ map g (map f xs)
map-∘ _ _ [] = refl
map-∘ _ _ (_ ∷ _) = cong (_∷_ _) (map-∘ _ _ _)

instance
  vecEndofunctor : Endofunctor setCategory (λ a → Vec a n)
  vecEndofunctor = record
    { map = map
    ; map-id = ext map-id
    ; map-∘ = λ f g → ext (map-∘ f g)
    }

mapCommutesOverLookup : ∀
  {ℓ m}
  {a b : Set ℓ}
  {f : a → b}
  (xs : Vec a m)
  (i : Fin m)
  →
  lookup i (map f xs) ≡ f (lookup i xs)
mapCommutesOverLookup [] ()
mapCommutesOverLookup (_ ∷ _) zero = refl
mapCommutesOverLookup (_ ∷ _) (suc i) = mapCommutesOverLookup _ i

mapCommutesOverTabulate : ∀
  {ℓ m}
  {a b : Set ℓ}
  (f : a → b)
  (tab : Fin m → a)
  →
  tabulate (f ∘ tab) ≡ map f (tabulate tab)
mapCommutesOverTabulate {m = zero} _ tab = refl
mapCommutesOverTabulate {m = suc m} f tab = cong (_∷_ (f (tab zero))) (mapCommutesOverTabulate f (tab ∘ suc))

lookupTabulateCancel : ∀
  {ℓ m}
  {a : Set ℓ}
  (tab : Fin m → a)
  (i : Fin m)
  →
  lookup i (tabulate tab) ≡ tab i
lookupTabulateCancel tab zero = refl
lookupTabulateCancel tab (suc i) = lookupTabulateCancel (tab ∘ suc) i

tabulateLookupCancel : ∀
  {ℓ m}
  {a : Set ℓ}
  (xs : Vec a m)
  →
  tabulate (flip lookup xs) ≡ xs
tabulateLookupCancel [] = refl
tabulateLookupCancel (_ ∷ _) = cong (_∷_ _) (tabulateLookupCancel _)

instance
  vecRepresentable :
    Representable
      vecEndofunctor
      (λ _ xs i → lookup (lower i) xs)
      (λ _ f → tabulate (λ i → f (lift i)))
  vecRepresentable = record
    { rightNT = record
        { naturality = λ _ → ext λ xs → ext λ i → mapCommutesOverLookup xs (lower i)
        }
    ; leftNT = record
        { naturality = λ f → ext λ g → mapCommutesOverTabulate f (λ i → g (lift i))
        }
    ; leftId = λ _ → ext λ tab → ext λ i → lookupTabulateCancel (λ x → tab (lift x)) (lower i)
    ; rightId = λ _ → ext tabulateLookupCancel
    }
