module Structures.UniversalProduct where

open import Data.Product

open import Axioms

open import Structures.Category
open import Structures.Product public

open Category {{...}}
open Product {{...}} public

record UniversalProduct
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (a b c : O)
  :
  Set (ℓ₁ ⊔ ℓ₂) where

  field
    product : Product cat a b c
    factor : ∀ {c′} → (p : c′ ⇒ a) → (q : c′ ⇒ b) → Σ[ m ∈ c′ ⇒ c ] ((p ≡ fst ∘ m) × (q ≡ snd ∘ m))

  -- without this, having a UniversalProduct opened in scope isn't enough to have the instance search for fst/snd
  -- find this instance - maybe there's a better way to structure it?
  instance
    productProduct : Product cat a b c
    productProduct = product
