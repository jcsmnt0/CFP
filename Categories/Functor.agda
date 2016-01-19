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

cong-_,_ : ∀
  {ℓ₁ ℓ₂}
  {a : Set ℓ₁}
  {b : a → Set ℓ₂} 
  {x y : a}
  {u : b x}
  {v : b y}
  (p : x ≡ y)
  (q : subst b p u ≡ v)
  →
  (x , u) ≡ (y , v)
cong-_,_ refl refl = refl

-- if all of functorF, functorG, and α in the types of the NTs are definitionally equal, the NTs themselves
-- are equal, because the only other component of a natural transformation is the evidence for the naturality
-- condition, and all functions returning equality proofs of the same type are equal given axiom K and
-- extensionality.
congNT : ∀
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {Oᵅ : Set ℓ₂}
  {_⇒_ : O → O → Set ℓ₃} {_⇒ᵅ_ : Oᵅ → Oᵅ → Set ℓ₄}
  {cat : Category O _⇒_} {catᵅ : Category Oᵅ _⇒ᵅ_}
  {F : O → Oᵅ} {G : O → Oᵅ}
  {functorF : Functor cat catᵅ F} {functorG : Functor cat catᵅ G}
  {α : ∀ a → F a ⇒ᵅ G a}
  {nt nt′ : NaturalTransformation functorF functorG α}
  →
  nt ≡ nt′
congNT = cong NT (ext-implicit λ _ → ext-implicit λ _ → ext λ _ → K)

assocᶠ : ∀ {a b c d} (h : c ⇒ᶠ d) (g : b ⇒ᶠ c) (f : a ⇒ᶠ b) → h ∘ᶠ (g ∘ᶠ f) ≡ (h ∘ᶠ g) ∘ᶠ f
assocᶠ _ _ _ = cong-_,_ (ext λ _ → assoc _ _ _) congNT

cancelLeftᶠ : ∀ {a b} {f : a ⇒ᶠ b} → idᶠ ∘ᶠ f ≡ f
cancelLeftᶠ {f = α , nt} = cong-_,_ (ext (λ x → cancelLeft)) congNT

cancelRightᶠ : ∀ {a b} {f : a ⇒ᶠ b} → f ∘ᶠ idᶠ ≡ f
cancelRightᶠ {f = f} = cong-_,_ (ext (λ x → cancelRight)) congNT

instance
  functorCategory : Category Oᶠ _⇒ᶠ_
  functorCategory = record
    { _∘_ = _∘ᶠ_
    ; id = idᶠ
    ; assoc = assocᶠ
    ; cancelLeft = cancelLeftᶠ
    ; cancelRight = cancelRightᶠ
    }

