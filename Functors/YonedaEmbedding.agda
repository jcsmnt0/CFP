open import Structures.Category

module Functors.YonedaEmbedding
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  where

open import Data.Product using (<_,_>; _,_; ,_)

open import Axioms

open import Structures.Functor
open import Structures.NaturalIsomorphism
open import Structures.NaturalTransformation

open import Categories.SetCat ℓ₂
open import Categories.Functor cat setCategory

open import Functors.HomFunctor cat

open import NaturalTransformations.Yoneda cat

open Category {{...}}
open Functor {{...}}
open NaturalIsomorphism YonedaLemma
open NaturalTransformation rightNT

embed : O → Oᶠ
embed = < HomSet , homFunctor >

mapYE : ∀ {a b} → (a ⇒ b) → (embed b ⇒ᶠ embed a)
mapYE {a} {b} f = functor→NT ((, homFunctor a) , b) (lift f)

mapYE-id : ∀ {a} → mapYE {a} id ≡ id
mapYE-id {a} = cong⟨ (ext λ _ → ext λ _ → cancelRight) , congNT ⟩

mapYE-∘ : {a b c : O} (f : b ⇒ a) (g : c ⇒ b) → mapYE (f ∘ g) ≡ mapYE g ∘ mapYE f
mapYE-∘ _ _ = cong⟨ (ext λ _ → ext λ _ → assoc _ _ _) , congNT ⟩

YonedaEmbedding : Contrafunctor cat functorCategory embed
YonedaEmbedding = record
  { map = mapYE
  ; map-id = λ {a} → mapYE-id {a}
  ; map-∘ = mapYE-∘
  }
