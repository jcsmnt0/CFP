open import Structures.Category

module Functors.CoYonedaEmbedding
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  where

open import Data.Product using (<_,_>; _,_; proj₁)

open import Axioms

open import Structures.Functor
open import Structures.NaturalTransformation

open import Categories.SetCat ℓ₂
open import Categories.Contrafunctor cat setCategory
open import Functors.HomContrafunctor cat

open Category cat

coembed : O → Oᶠ
coembed = < ContraHomSet , homContrafunctor >

coYonedaEmbeddingFunctor : Functor cat contrafunctorCategory coembed
coYonedaEmbeddingFunctor = record
  { map = λ f → (λ _ → λ g → f ∘ g) , record { naturality = λ _ → ext λ _ → assoc _ _ _ }
  ; map-id = cong⟨ (ext λ _ → ext λ _ → cancelLeft) , congNT ⟩
  ; map-∘ = λ _ _ → cong⟨ (ext λ _ → ext λ _ → sym (assoc _ _ _)) , congNT ⟩
  }
