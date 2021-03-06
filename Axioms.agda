module Axioms where -- and miscellaneous imports and lemmas that several of these files need

open import Function using (const; flip) public
open import Level renaming (zero to lzero; suc to lsuc) public
open import Relation.Binary.PropositionalEquality public
open ≡-Reasoning public

-- simplified - the actual K axiom can be recovered by combining this with subst
K : ∀ {ℓ} {a : Set ℓ} {x y : a} {p q : x ≡ y} → p ≡ q
K {p = refl} {q = refl} = refl

postulate
  ext : ∀
    {ℓ₁ ℓ₂}
    {a : Set ℓ₁}
    {b : a → Set ℓ₂}
    {f g : (x : a) → b x}
    (p : ∀ x → f x ≡ g x)
    →
    f ≡ g

  ext-implicit : ∀
    {ℓ₁ ℓ₂}
    {a : Set ℓ₁}
    {b : a → Set ℓ₂}
    {f g : ∀ {x} → b x}
    (p : ∀ x → f {x} ≡ g {x})
    →
    (λ {x} → f {x}) ≡ g

_$$_ : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : a → Set ℓ₂} {f g : (x : a) → b x} → f ≡ g → ∀ x → f x ≡ g x
refl $$ _ = refl

open import Data.Product

cong⟨_,_⟩ : ∀
  {ℓ₁ ℓ₂}
  {a : Set ℓ₁}
  {b : a → Set ℓ₂} 
  {x y : a}
  {u : b x}
  {v : b y}
  (p : x ≡ y)
  (q : subst b p u ≡ v)
  →
  (x , u) ≡ (y , v)
cong⟨ refl , refl ⟩ = refl
