module Categories.SetCat.TerminalObject ℓ where

open import Axioms

open import Categories.SetCat ℓ

open import Structures.TerminalObject

data ⊤ : Set ℓ where tt : ⊤

⊤-uniqueness : ∀ {x y : ⊤} → x ≡ y
⊤-uniqueness {tt} {tt} = refl

instance
  ⊤-initial : TerminalObject setCategory ⊤
  ⊤-initial = record
    { terminal = const tt
    ; uniqueness = ext (λ _ → ⊤-uniqueness)
    }
