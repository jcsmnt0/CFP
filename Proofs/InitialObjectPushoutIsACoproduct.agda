open import Structures.Category

module Proofs.InitialObjectPushoutIsACoproduct
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  {a b : O}
  (cat : Category O _⇒_)
  (c : O)
  (⊥ : O)
  (f : ⊥ ⇒ a)
  (g : ⊥ ⇒ b)
  where

open import Axioms

open import Structures.Pushout cat f g
open import Structures.InitialObject
open import Structures.UniversalCoproduct
open import Structures.UniversalProduct

open Category {{...}}

open import Proofs.InitialObject cat
open import Proofs.Product op
open import Proofs.TerminalObjectPullbackIsAProduct op c ⊥ f g

pushoutProduct : Pushout c → InitialObject cat ⊥ → UniversalProduct op a b c
pushoutProduct pushout initialObject =
  terminalObjectPullback-UniversalProduct
    pushout
    (initialObjectDualOfTerminalObject initialObject)

initialObjectPushout-UniversalCoproduct : Pushout c → InitialObject cat ⊥ → UniversalCoproduct cat a b c
initialObjectPushout-UniversalCoproduct pushout initialObject =
  subst
    (λ x → UniversalCoproduct x a b c)
    (cancelDoubleDual cat)
    (universalProductDualOfUniversalCoproduct (pushoutProduct pushout initialObject))
