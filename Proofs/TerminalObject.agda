open import Structures.Category

module Proofs.TerminalObject
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_) where

open import Axioms

open import Structures.InitialObject
open import Structures.TerminalObject

open Category {{...}}
open TerminalObject {{...}}

terminalObjectUniqueUpToIsomorphism : ∀ {a b} → TerminalObject cat a → TerminalObject cat b → a ⇔ b
terminalObjectUniqueUpToIsomorphism _ _ = record
  { right = terminal
  ; left = terminal
  ; rightInverse = trans (uniqueness {m = terminal ∘ terminal}) (sym (uniqueness {m = id}))
  ; leftInverse = trans (uniqueness {m = terminal ∘ terminal}) (sym (uniqueness {m = id}))
  }

terminalObjectDualOfInitialObject : ∀ {a} → TerminalObject cat a → InitialObject op a
terminalObjectDualOfInitialObject _ = record
  { initial = terminal
  ; uniqueness = uniqueness
  }
