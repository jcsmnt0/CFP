open import Relation.Binary

open import Axioms

module Categories.Preorder
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_≤_ : O → O → Set ℓ₂}
  (isPreorder : IsPreorder _≡_ _≤_)
  (≤-uniqueness : ∀ {a b} {p q : a ≤ b} → p ≡ q)
  where

open import Data.Product using (proj₁; proj₂)

open import Structures.Category

open IsPreorder isPreorder renaming (trans to trans-≤; refl to refl-≤)

instance
  preorderCategory : Category O _≤_
  preorderCategory = record
    { _∘_ = flip trans-≤
    ; id = refl-≤
    ; cancelLeft = ≤-uniqueness
    ; cancelRight = ≤-uniqueness
    ; assoc = λ _ _ _ → ≤-uniqueness
    }
