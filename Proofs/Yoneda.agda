open import Structures.Category
open import Structures.Functor

module Proofs.Yoneda
  {ℓ}
  {O : Set ℓ}
  {_⇒_ : O → O → Set ℓ}
  {F : O → Set ℓ}
  (cat : Category O _⇒_)
  where

open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)

open import Axioms
open import Function using (_∘_)

open import Structures.NaturalTransformation

open import Categories.SetCat ℓ

open import Functors.HomFunctor cat

open Category {{...}}
open Functor {{...}}
open NaturalTransformation {{...}}

-- this is all supposed to form a natural isomorphism between two (Setᴼ × O) → Set functors somehow?

yonedaRight : ∀
  {a : O}
  {F : O → Set ℓ}
  {functorF : Functor cat setCategory F}
  (nt : ∃ (NaturalTransformation (homFunctor a) functorF))
  →
  F a
yonedaRight (α , _) = α _ id

yonedaLeft : ∀
  {a : O}
  {F : O → Set ℓ}
  (functorF : Functor cat setCategory F)
  (x : F a)
  →
  ∃ (NaturalTransformation (homFunctor a) functorF)
yonedaLeft functorF x = (λ _ → flip map x) , record { naturality = λ f → ext λ g → map-∘ g f $$ x }

yonedaRightId : ∀
  {a : O}
  {F : O → Set ℓ}
  {functorF : Functor cat setCategory F}
  (nt : ∃ (NaturalTransformation (homFunctor a) functorF))
  →
  nt ≡ yonedaLeft functorF (yonedaRight nt)
yonedaRightId {a = a} {functorF = functorF} (α , nt) =
  cong⟨ (ext λ x → ext λ f → trans (cong (α x) (sym cancelRight)) (naturality f $$ id)) , congNT ⟩

yonedaLeftId : ∀
  {a : O}
  {F : O → Set ℓ}
  (functorF : Functor cat setCategory F)
  (x : F a)
  →
  x ≡ yonedaRight (yonedaLeft functorF x)
yonedaLeftId functorF x = sym map-id $$ x
