open import Structures.Category

module Categories.Functor
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₃}
  {_⇒_ : O → O → Set ℓ₂} {_⇒′_ : O′ → O′ → Set ℓ₄}
  (cat : Category O _⇒_) (cat′ : Category O′ _⇒′_) 
  where

open import Data.Product using (∃; _,_)

open import Axioms

open import Structures.Functor
open import Structures.NaturalTransformation

open Category {{...}}
open Functor {{...}}
open NaturalTransformation {{...}}

Oᶠ : Set _
Oᶠ = ∃ (Functor cat cat′)

_⇒ᶠ_ : Oᶠ → Oᶠ → Set _
(_ , f) ⇒ᶠ (_ , g) = ∃ (NaturalTransformation f g)

_∘ᶠ_ : ∀ {a b c} → b ⇒ᶠ c → a ⇒ᶠ b → a ⇒ᶠ c
_∘ᶠ_ {_ , a} {_ , b} {_ , c} (G , g) (F , f) = (λ x → G x ∘ F x) , record
  { naturality = λ {x} {y} h →
      begin
        (G y ∘ F y) ∘ map h
      ≡⟨ sym (assoc _ _ _) ⟩
        G y ∘ (F y ∘ map h)
      ≡⟨ cong (_∘_ (G y)) (naturality h) ⟩
        G y ∘ (map h ∘ F x)
      ≡⟨ assoc _ _ _ ⟩
        (G y ∘ map h) ∘ F x
      ≡⟨ cong (flip _∘_ (F x)) (naturality h) ⟩
        (map h ∘ G x) ∘ F x
      ≡⟨ sym (assoc _ _ _) ⟩
        map h ∘ (G x ∘ F x)
      ∎
  }

idᶠ : ∀ {a} → a ⇒ᶠ a
idᶠ = (λ _ → id) , record { naturality = λ _ → trans cancelLeft (sym cancelRight) }

assocᶠ : ∀ {a b c d} (h : c ⇒ᶠ d) (g : b ⇒ᶠ c) (f : a ⇒ᶠ b) → h ∘ᶠ (g ∘ᶠ f) ≡ (h ∘ᶠ g) ∘ᶠ f
assocᶠ _ _ _ = cong⟨ (ext λ _ → assoc _ _ _) , congNT ⟩

cancelLeftᶠ : ∀ {a b} {f : a ⇒ᶠ b} → idᶠ ∘ᶠ f ≡ f
cancelLeftᶠ {f = α , nt} = cong⟨ (ext (λ x → cancelLeft)) , congNT ⟩

cancelRightᶠ : ∀ {a b} {f : a ⇒ᶠ b} → f ∘ᶠ idᶠ ≡ f
cancelRightᶠ {f = f} = cong⟨ (ext (λ x → cancelRight)) , congNT ⟩

instance
  functorCategory : Category Oᶠ _⇒ᶠ_
  functorCategory = record
    { _∘_ = _∘ᶠ_
    ; id = idᶠ
    ; assoc = assocᶠ
    ; cancelLeft = cancelLeftᶠ
    ; cancelRight = cancelRightᶠ
    }

