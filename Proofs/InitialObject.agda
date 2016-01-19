open import Structures.Category

module Proofs.InitialObject
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  where

open import Axioms

open import Structures.InitialObject
open import Structures.TerminalObject

open Category {{...}}
open InitialObject {{...}}

initialObjectUniqueUpToIsomorphism : ∀ {a b} → InitialObject cat a → InitialObject cat b → a ⇔ b
initialObjectUniqueUpToIsomorphism _ _ = record
  { right = initial
  ; left = initial
  ; rightInverse = trans (uniqueness {m = initial ∘ initial}) (sym (uniqueness {m = id}))
  ; leftInverse = trans (uniqueness {m = initial ∘ initial}) (sym (uniqueness {m = id}))
  }

initialObjectDualOfTerminalObject : ∀ {a} → InitialObject cat a → TerminalObject op a
initialObjectDualOfTerminalObject _ = record
  { terminal = initial
  ; uniqueness = uniqueness
  }
