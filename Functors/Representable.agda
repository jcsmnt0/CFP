module Functors.Representable where

open import Axioms

open import Categories.SetCat

open import Functors.HomFunctor

open import Structures.Category
open import Structures.Functor
open import Structures.NaturalIsomorphism

Representable : ∀
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  {cat : Category O _⇒_}
  {F : O → Set ℓ₂}
  {a : O}
  (functorF : Functor cat (setCategory ℓ₂) F)
  (index : ∀ b → F b → (a ⇒ b))
  (tabulate : ∀ b → (a ⇒ b) → F b)
  →
  Set (ℓ₁ ⊔ suc ℓ₂)
Representable {cat = cat} {a = a} functorF index tabulate =
  NaturalIsomorphism functorF (homFunctor cat a) index tabulate
