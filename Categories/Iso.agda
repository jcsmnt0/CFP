open import Structures.Category

module Categories.Iso
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  where

open import Axioms

open Category cat

record Iso (a b : O) : Set ℓ₂ where
  constructor iso

  field
    right : a ⇒ b
    left : b ⇒ a
    rightInverse : right ∘ left ≡ id
    leftInverse : left ∘ right ≡ id

congIso : ∀
  {a b}
  {f f′ : a ⇒ b}
  {g g′ : b ⇒ a}
  {rightInverse : f ∘ g ≡ id}
  {rightInverse′ : f′ ∘ g′ ≡ id}
  {leftInverse : g ∘ f ≡ id}
  {leftInverse′ : g′ ∘ f′ ≡ id}
  (p : f ≡ f′)
  (q : g ≡ g′)
  →
  iso f g rightInverse leftInverse ≡ iso f′ g′ rightInverse′ leftInverse′
congIso refl refl = cong₂ (iso _ _) K K

_⇔_ : ∀ a b → Set ℓ₂
_⇔_ = Iso

open Iso {{...}}

id-⇔ : ∀ {a} → (a ⇔ a)
id-⇔ = record
  { right = id
  ; left = id
  ; rightInverse = cancelRight
  ; leftInverse = cancelLeft
  }

_⟨∘⟩_ : ∀ {a b c} → (b ⇔ c) → (a ⇔ b) → (a ⇔ c)
g ⟨∘⟩ f = record
  { right = right ∘ right
  ; left = left ∘ left
  ; rightInverse =
      begin
        (right ∘ right) ∘ (left ∘ left)
      ≡⟨ assoc _ _ _ ⟩
        ((right ∘ right) ∘ left) ∘ left
      ≡⟨ cong-∘ᴸ (sym (assoc _ _ _)) ⟩
        (right ∘ (right ∘ left)) ∘ left
      ≡⟨ cong-∘ᴸ (cong-∘ᴿ rightInverse) ⟩
        (right ∘ id) ∘ left
      ≡⟨ cong-∘ᴸ cancelRight ⟩
        right ∘ left
      ≡⟨ rightInverse ⟩
        id
      ∎
  ; leftInverse =
      begin
        (left ∘ left) ∘ (right ∘ right)
      ≡⟨ assoc _ _ _ ⟩
        ((left ∘ left) ∘ right) ∘ right
      ≡⟨ cong-∘ᴸ (sym (assoc _ _ _)) ⟩
        (left ∘ (left ∘ right)) ∘ right
      ≡⟨ cong-∘ᴸ (cong-∘ᴿ leftInverse) ⟩
        (left ∘ id) ∘ right
      ≡⟨ cong-∘ᴸ cancelRight ⟩
        left ∘ right
      ≡⟨ leftInverse ⟩
        id
      ∎
  }

cancelLeft-⇔ : ∀ {a b} {f : a ⇔ b} → id-⇔ ⟨∘⟩ f ≡ f
cancelLeft-⇔ = congIso cancelLeft cancelRight

cancelRight-⇔ : ∀ {a b} {f : a ⇔ b} → f ⟨∘⟩ id-⇔ ≡ f
cancelRight-⇔ = congIso cancelRight cancelLeft

assoc-⇔ : ∀ {a b c d} (h : c ⇔ d) (g : b ⇔ c) (f : a ⇔ b) → h ⟨∘⟩ (g ⟨∘⟩ f) ≡ (h ⟨∘⟩ g) ⟨∘⟩ f
assoc-⇔ h g f = congIso (assoc _ _ _) (sym (assoc _ _ _))

instance
  isoCategory : Category O _⇔_
  isoCategory = record
    { _∘_ = _⟨∘⟩_
    ; id = id-⇔
    ; cancelLeft = cancelLeft-⇔
    ; cancelRight = cancelRight-⇔
    ; assoc = assoc-⇔
    }
