open import Structures.Category

module Structures.Pushout
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  {a b c : O}
  (f : b ⇒ a)
  (g : b ⇒ c)
  where

open import Axioms

open Category cat

open import Structures.Pullback op f g

Pushout : O → Set (ℓ₁ ⊔ ℓ₂)
Pushout = Pullback
