open import Data.Nat

module Categories.SetCat.VecEndofunctor where

open import Data.Fin hiding (lift)
open import Data.Product using (∃; _,_; ,_; proj₁; proj₂)
open import Data.Vec as Vec using (Vec; []; _∷_; replicate; _⊛_)
open import Function using (id; _∘_)

open import Axioms

open import Structures.Endofunctor
open import Structures.NaturalIsomorphism
open import Structures.NaturalTransformation

open import Categories.Iso
open import Categories.SetCat
open import Properties.Functor
open import Functors.HomFunctor
open import NaturalTransformations.Yoneda

lookup : ∀ {ℓ m} {a : Set ℓ} → Fin m → Vec a m → a
lookup () []
lookup zero (x ∷ _) = x
lookup (suc i) (_ ∷ xs) = lookup i xs

map : ∀ {ℓ₁ ℓ₂ m} {a : Set ℓ₁} {b : Set ℓ₂} → (a → b) → Vec a m → Vec b m
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-id : ∀ {ℓ m} {a : Set ℓ} (xs : Vec a m) → map id xs ≡ xs
map-id [] = refl
map-id (_ ∷ _) = cong (_∷_ _) (map-id _)

map-∘ : ∀
  {ℓ₁ ℓ₂ ℓ₃ m}
  {a : Set ℓ₁}
  {b : Set ℓ₂}
  {c : Set ℓ₃}
  (f : a → b)
  (g : b → c)
  (xs : Vec a m)
  →
  map (g ∘ f) xs ≡ map g (map f xs)
map-∘ _ _ [] = refl
map-∘ _ _ (_ ∷ _) = cong (_∷_ _) (map-∘ _ _ _)

vecEndofunctor : ∀ {ℓ} n → Endofunctor (setCategory ℓ) (λ a → Vec a n)
vecEndofunctor _ = record
  { map = map
  ; map-id = ext map-id
  ; map-∘ = λ f g → ext (map-∘ f g)
  }

allFin : ∀ {n} → Vec (Fin n) n
allFin {zero} = []
allFin {suc n} = zero ∷ map suc allFin

tabulateNT : ∀ {ℓ n} → ∃ (NaturalTransformation (homFunctor _ (Lift (Fin n))) (vecEndofunctor {ℓ} n))
tabulateNT {ℓ} {n} = functor→NT _ _ (lift (map lift allFin))
  where
    open Iso _ (yonedaIso (setCategory ℓ) {a = Lift (Fin n)} {functorF = vecEndofunctor n})

tabulate : ∀ {ℓ n} (a : Set ℓ) → (Lift (Fin n) → a) → Vec a n
tabulate _ = proj₁ tabulateNT _

tabulate-naturality : ∀ {ℓ n} → NaturalTransformation (homFunctor _ (Lift (Fin n))) (vecEndofunctor {ℓ} n) tabulate
tabulate-naturality = proj₂ tabulateNT

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
mapCommutesOverLookup (_ ∷ xs) (suc i) = mapCommutesOverLookup xs i

lookupTabulateCancel : ∀
  {ℓ m}
  {a : Set ℓ}
  (tab : Fin m → a)
  →
  flip lookup (tabulate _ (tab ∘ lower)) ≡ tab
lookupTabulateCancel {ℓ} {a = a} tab =
  begin
    flip lookup (map (tab ∘ lower) (map lift allFin))
  ≡⟨ cong (flip lookup) (map-∘ _ _ (map lift allFin)) ⟩
    flip lookup (map tab (map (lower {ℓ = ℓ}) (map lift allFin)))
  ≡⟨ cong (flip lookup ∘ map tab) (sym (map-∘ lift (lower {ℓ = ℓ}) allFin)) ⟩
    flip lookup (map tab (map id allFin))
  ≡⟨ cong (flip lookup ∘ map tab) (map-id allFin) ⟩
    flip lookup (map tab allFin)
  ≡⟨ ext (lemma tab) ⟩
    tab
  ∎
  where
    lemma : ∀ {n} (tab′ : Fin n → a) (i : Fin n) → lookup i (map tab′ allFin) ≡ tab′ i
    lemma tab′ zero = refl
    lemma tab′ (suc i) =
      begin
        lookup i (map tab′ (map suc allFin))
      ≡⟨ cong (lookup i) (sym (map-∘ _ _ allFin)) ⟩
        lookup i (map (tab′ ∘ suc) allFin)
      ≡⟨ lemma (tab′ ∘ suc) i ⟩
        tab′ (suc i)
      ∎

tabulateLookupCancel : ∀
  {ℓ m}
  {a : Set ℓ}
  (xs : Vec a m)
  →
  tabulate _ (flip lookup xs ∘ lower) ≡ xs
tabulateLookupCancel [] = refl
tabulateLookupCancel {ℓ} (x ∷ xs) =
  cong (_∷_ _) (
    begin
      map (flip lookup (x ∷ xs) ∘ lower) (map lift (map suc allFin))
    ≡⟨ sym (map-∘ _ _ _) ⟩
      map (flip lookup (x ∷ xs) ∘ lower {ℓ = ℓ} ∘ lift) (map suc allFin)
    ≡⟨ refl ⟩
      map (flip lookup (x ∷ xs)) (map suc allFin)
    ≡⟨ sym (map-∘ _ _ _) ⟩
      map (flip lookup (x ∷ xs) ∘ suc) allFin
    ≡⟨ refl ⟩
      map (flip lookup xs) allFin
    ≡⟨ refl ⟩
      map (flip lookup xs ∘ lower {ℓ = ℓ} ∘ lift) allFin
    ≡⟨ map-∘ _ _ _ ⟩
      map (flip lookup xs ∘ lower {ℓ = ℓ}) (map lift allFin)
    ≡⟨ tabulateLookupCancel xs ⟩
      xs
    ∎)

vecRepresentable : ∀ {ℓ n} → Representable (vecEndofunctor {ℓ} n) (λ _ xs i → lookup (lower i) xs) tabulate
vecRepresentable {ℓ = ℓ} {n = n} = record
  { rightNT = record { naturality = λ _ → ext λ xs → ext λ i → mapCommutesOverLookup xs (lower i) }
  ; leftNT = tabulate-naturality
  ; leftId = λ _ → ext λ tab → ext λ i → lookupTabulateCancel (tab ∘ lift) $$ lower i
  ; rightId = λ _ → ext tabulateLookupCancel
  }
