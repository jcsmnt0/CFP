-- some instances of the Yoneda lemma and Yoneda embedding
module Proofs.Yoneda where

open import Data.Product using (∃; _,_; ,_; proj₁; proj₂)

open import Axioms
open import Lemmas

open import Structures.Category
open import Structures.Functor
open import Structures.NaturalIsomorphism
open import Structures.NaturalTransformation

open import Functors.CoYonedaEmbedding
open import Functors.YonedaEmbedding

open import NaturalTransformations.CoYoneda
open import NaturalTransformations.Yoneda

module Preorder where
  open import Data.Nat
  open import Relation.Binary

  open DecTotalOrder decTotalOrder using () renaming (isPreorder to ≤-isPreorder; trans to ≤-trans)

  open import Categories.Preorder ≤-isPreorder ≤-uniqueness

  open import Functors.HomContrafunctor preorderCategory

  open Category preorderCategory

  ≤-NT : ∀ {a b} (α : ∀ x → x ≤ a → x ≤ b) → NaturalTransformation (homContrafunctor a) (homContrafunctor b) α
  ≤-NT _ = record { naturality = λ _ → ext λ _ → ≤-uniqueness }

  yonedaLR : ∀ {a b} → (∀ x → x ≤ a → x ≤ b) → a ≤ b
  yonedaLR p = lower (NT→contrafunctor _ _ (, ≤-NT p)) 

  yonedaRL : ∀ {a b} → a ≤ b → ∀ x → x ≤ a → x ≤ b
  yonedaRL {a} {b} p x q = proj₁ (contrafunctor→NT _ ((, homContrafunctor b) , a) (lift p)) x q 

module Vec ℓ where
  open import Data.Vec hiding (tabulate)

  open import Categories.SetCat ℓ
  open import Categories.SetCat.VecEndofunctor ℓ

  open import Functors.HomFunctor setCategory

  open Category setCategory

  yonedaLR : ∀ {a : Set ℓ} {n α} → NaturalTransformation (homFunctor a) (vecEndofunctor n) α → Vec a n
  yonedaLR nt-α = lower (NT→functor _ _ (, nt-α))

  yonedaRL : ∀ {a n} → Vec a n → ∃ (NaturalTransformation (homFunctor a) (vecEndofunctor n))
  yonedaRL {a} {n} x = functor→NT _ ((, vecEndofunctor n) , a) (lift x)

module Fin (ℓ : Level) where
  open import Data.Empty
  open import Data.Fin hiding (lift; _≤_)
  open import Data.Nat
  open import Relation.Binary
  open import Relation.Nullary

  open DecTotalOrder decTotalOrder using () renaming (isPreorder to ≤-isPreorder; trans to ≤-trans)

  open import Categories.Preorder ≤-isPreorder ≤-uniqueness
  open import Categories.SetCat ℓ

  open import Functors.Fin
  open import Functors.HomFunctor preorderCategory

  finZeroEmpty : ¬ (Fin 0)
  finZeroEmpty ()

  yonedaLR : ∀ {n : ℕ} {α} → NaturalTransformation (homFunctor n) finFunctor α → Fin n
  yonedaLR {α = α} nt = lower (NT→functor _ _ (, nt))

  yonedaRL : ∀ {n} → Fin n → ∃ (NaturalTransformation (homFunctor n) finFunctor)
  yonedaRL {n} i = functor→NT _ ((, finFunctor) , n) (lift i)

  fromℕ≤′ : ∀ {m} → Fin m → ∀ n → (m ≤ n) → Fin n
  fromℕ≤′ i = proj₁ (yonedaRL i)
