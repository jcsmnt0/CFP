-- some instances of the Yoneda lemma and Yoneda embedding
module Proofs.Yoneda where

open import Data.Product using (∃; _,_; ,_; proj₁; proj₂)
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_)

open import Axioms
open import Lemmas

open import Structures.Category
open import Structures.Functor
open import Structures.InitialObject
open import Structures.NaturalIsomorphism
open import Structures.NaturalTransformation

open import Categories.Iso
open import Categories.SetCat

-- this is some kind of functor
lowerIso : ∀
  {ℓ ℓ′}
  {a b : Set ℓ}
  →
  let
    _≈_ = _⇔_ (setCategory ℓ)
    _≈′_ = _⇔_ (setCategory (ℓ ⊔ ℓ′))
  in
    Lift {ℓ = ℓ′} a ≈′ Lift {ℓ = ℓ′} b → a ≈ b
lowerIso p = record
  { right = λ x → lower (right (lift x))
  ; left = λ x → lower (left (lift x))
  ; rightInverse = ext λ x → cong lower (rightInverse $$ lift x)
  ; leftInverse = ext λ x → cong lower (leftInverse $$ lift x)
  }
  where open Iso _ p

_≈_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
_≈_ {ℓ} = _⇔_ (setCategory ℓ)

module YonedaPreorder where
  open import Data.Nat hiding (_⊔_)
  open import Relation.Binary

  open DecTotalOrder decTotalOrder using () renaming (isPreorder to ≤-isPreorder; trans to ≤-trans)

  open import Categories.Preorder ≤-isPreorder ≤-uniqueness
  open import Functors.HomContrafunctor preorderCategory
  open import NaturalTransformations.CoYoneda preorderCategory
  open import NaturalTransformations.Yoneda preorderCategory

  open Category (isoCategory (setCategory (lsuc lzero)))
  open NaturalIsomorphism coYonedaLemma

  yonedaPreorder : ∀ {a b} → (∀ x → a ≤ x → b ≤ x) ≈ (b ≤ a)
  yonedaPreorder = lowerIso (yonedaIso ∘ ≤-isoNT)

  coYonedaPreorder : ∀ {a b} → (∀ x → x ≤ a → x ≤ b) ≈ (a ≤ b)
  coYonedaPreorder = lowerIso (coYonedaIso ∘ ≤-isoContraNT)
  
module YonedaVec ℓ n where
  open import Data.Fin hiding (lift)
  open import Data.Vec

  open import Categories.SetCat.VecEndofunctor ℓ n
  open import Functors.HomFunctor (setCategory ℓ)
  open import NaturalTransformations.Yoneda (setCategory ℓ)

  open Category (setCategory ℓ)
  open NaturalIsomorphism vecRepresentable

  yonedaVec : ∀ {a} → ∃ (NaturalTransformation (homFunctor a) vecEndofunctor) ≈ Lift (Vec a n)
  yonedaVec = yonedaIso

  allFin′ : Vec (Fin n) n
  allFin′ = map lower (lower (right (, leftNT)))
    where open Iso _ yonedaVec

module YonedaFin where
  open import Data.Fin hiding (lift; _≤_)
  open import Data.Nat
  open import Relation.Binary

  open DecTotalOrder decTotalOrder using () renaming (isPreorder to ≤-isPreorder; trans to ≤-trans)

  open import Categories.Preorder ≤-isPreorder ≤-uniqueness
  open import Categories.SetCat.FinFunctor
  open import Functors.HomFunctor preorderCategory
  open import NaturalTransformations.Yoneda preorderCategory

  yonedaFin : ∀ {n} → ∃ (NaturalTransformation (homFunctor (suc n)) finFunctor) ≈ Lift (Fin (suc n))
  yonedaFin = yonedaIso

  last : ∀ {n} → Fin (suc n)
  last = lower (right (, fromℕ≤-NT))
    where open Iso _ yonedaFin
