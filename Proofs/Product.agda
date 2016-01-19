open import Structures.Category

module Proofs.Product
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  where

open import Axioms

open import Structures.Coproduct
open import Structures.UniversalProduct
open import Structures.UniversalCoproduct

open Category {{...}}
open UniversalProduct {{...}}

productDualOfCoproduct : ∀ {a b c} → Product cat a b c → Coproduct op a b c
productDualOfCoproduct product = record
  { left = fst
  ; right = snd
  }

universalProductDualOfUniversalCoproduct : ∀ {a b c} → UniversalProduct cat a b c → UniversalCoproduct op a b c
universalProductDualOfUniversalCoproduct universalProduct = record
  { coproduct = productDualOfCoproduct product
  ; factor = factor
  }

