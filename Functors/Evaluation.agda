open import Axioms
open import Structures.Category

module Functors.Evaluation
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₂}
  {_⇒_ : O → O → Set ℓ₃} {_⇒′_ : O′ → O′ → Set ℓ₄}
  (cat : Category O _⇒_) (cat′ : Category O′ _⇒′_)
  where

open import Data.Product using (_×_; _,_)

open import Structures.Functor
open import Structures.NaturalTransformation

open import Categories.Functor cat cat′
open import Categories.Product functorCategory cat

open Category {{...}}
open Functor {{...}}
open NaturalTransformation {{...}}

evaluate : Oˣ → O′
evaluate ((F , functorF) , a) = F a

mapEval : ∀ {a b} → (a ⇒ˣ b) → evaluate a ⇒′ evaluate b
mapEval {(F , functorF) , a} ((α , nt) , f) = map f ∘ α a

mapEval-id : ∀ {a} → mapEval {a} id ≡ id
mapEval-id {(F , functorF) , a} = trans (cong-∘ᴸ map-id) cancelLeft

mapEval-∘ : ∀ {a b c} (f : a ⇒ˣ b) (g : b ⇒ˣ c) → mapEval (g ∘ f) ≡ mapEval g ∘ mapEval f
mapEval-∘ {a = _ , a} {b = _ , b} {c = (H , functorH) , c} ((α , nt-α) , f) ((β , nt-β) , g) =
  begin
    map (g ∘ f) ∘ (β a ∘ α a)
  ≡⟨ cong-∘ᴸ (map-∘ f g) ⟩
    (map g ∘ map f) ∘ (β a ∘ α a)
  ≡⟨ assoc _ _ _ ⟩
    ((map g ∘ map f) ∘ β a) ∘ α a
  ≡⟨ cong-∘ᴸ (sym (assoc _ _ _)) ⟩
    (map g ∘ (map f ∘ β a)) ∘ α a
  ≡⟨ cong-∘ᴸ (cong-∘ᴿ (sym (naturality {{nt-β}} f))) ⟩
    (map g ∘ (β b ∘ map f)) ∘ α a
  ≡⟨ cong-∘ᴸ (assoc _ _ _) ⟩
    ((map g ∘ β b) ∘ map f) ∘ α a
  ≡⟨ sym (assoc _ _ _) ⟩
    (map g ∘ β b) ∘ (map f ∘ α a)
  ∎

instance
  evaluationFunctor : Functor productCategory cat′ evaluate
  evaluationFunctor = record
    { map = mapEval
    ; map-id = λ {a} → mapEval-id {a}
    ; map-∘ = mapEval-∘
    }
