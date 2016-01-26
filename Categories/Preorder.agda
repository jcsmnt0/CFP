open import Relation.Binary

open import Axioms

module Categories.Preorder
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_≤_ : O → O → Set ℓ₂}
  (isPreorder : IsPreorder _≡_ _≤_)
  (≤-uniqueness : ∀ {a b} {p q : a ≤ b} → p ≡ q)
  where

open import Data.Product using (∃; proj₁; _,_)

open import Structures.Category
open import Structures.NaturalTransformation

open import Categories.SetCat (ℓ₁ ⊔ lsuc ℓ₂)
open import Categories.Iso setCategory using () renaming (_⇔_ to _≈_)

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

open import Functors.HomContrafunctor preorderCategory
open import Functors.HomFunctor preorderCategory

≤-isoNT : ∀
  {a b}
  →
  Lift {ℓ = lsuc ℓ₂} (∀ x → a ≤ x → b ≤ x) ≈ ∃ (NaturalTransformation (homFunctor a) (homFunctor b))
≤-isoNT = record
  { right = λ α → (lower α , record { naturality = λ _ → ext λ _ → ≤-uniqueness })
  ; left = λ nt → lift (proj₁ nt)
  ; rightInverse = ext λ _ → cong⟨ refl , congNT ⟩
  ; leftInverse = ext λ _ → refl
  }

≤-isoContraNT : ∀
  {a b}
  →
  Lift {ℓ = lsuc ℓ₂} (∀ x → x ≤ a → x ≤ b) ≈ ∃ (NaturalTransformation (homContrafunctor a) (homContrafunctor b))
≤-isoContraNT = record
  { right = λ α → (lower α , record { naturality = λ _ → ext λ _ → ≤-uniqueness })
  ; left = λ nt → lift (proj₁ nt)
  ; rightInverse = ext λ _ → cong⟨ refl , congNT ⟩
  ; leftInverse = ext λ _ → refl
  }
