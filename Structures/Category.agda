module Structures.Category where

open import Axioms

record Category {ℓ₁ ℓ₂} (O : Set ℓ₁) (_⇒_ : O → O → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor category
  infixr 4 _∘_

  field
    _∘_ : ∀ {a b c} → (b ⇒ c) → (a ⇒ b) → (a ⇒ c)
    id : ∀ {a} → (a ⇒ a)

    assoc : ∀ {a b c d} →
      (h : c ⇒ d) →
      (g : b ⇒ c) →
      (f : a ⇒ b) →
      h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

    cancelLeft : ∀ {a b} →
      {f : a ⇒ b} →
      id ∘ f ≡ f

    cancelRight : ∀ {a b} →
      {f : a ⇒ b} →
      f ∘ id ≡ f

  cong-∘ : ∀ {a b c} {f g : a ⇒ b} {h i : b ⇒ c} → h ≡ i → f ≡ g → h ∘ f ≡ i ∘ g
  cong-∘ = cong₂ _∘_

  cong-∘ᴸ : ∀ {a b c} {h i : b ⇒ c} {f : a ⇒ b} → h ≡ i → h ∘ f ≡ i ∘ f
  cong-∘ᴸ = flip cong-∘ refl

  cong-∘ᴿ : ∀ {a b c} {h : b ⇒ c} {f g : a ⇒ b} → f ≡ g → h ∘ f ≡ h ∘ g
  cong-∘ᴿ = cong-∘ refl

  _∘ : ∀ {a b c} → (b ⇒ c) → (a ⇒ b) → (a ⇒ c)
  _∘ = _∘_

  ∘_ : ∀ {a b c} → (a ⇒ b) → (b ⇒ c) → (a ⇒ c)
  ∘_ = flip _∘_
 
  _⇐_ : O → O → Set ℓ₂
  _⇐_ = flip _⇒_

  _op∘_ : ∀ {a b c} → (b ⇐ c) → (a ⇐ b) → (a ⇐ c)
  g op∘ f = f ∘ g

  op : Category O _⇐_
  op = record
    { _∘_ = _op∘_
    ; id = id
    ; assoc = λ f g h → sym (assoc h g f)
    ; cancelLeft = cancelRight
    ; cancelRight = cancelLeft
    }

  -- categorical isomorphism
  record _⇔_ (a b : O) : Set (ℓ₁ ⊔ ℓ₂) where
    field
      right : a ⇒ b
      left : b ⇒ a
      rightInverse : right ∘ left ≡ id
      leftInverse : left ∘ right ≡ id

  HomSet : O → O → Set ℓ₂
  HomSet = _⇒_

  ContraHomSet : O → O → Set ℓ₂
  ContraHomSet = _⇐_

cancelDoubleDual : ∀
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  → Category.op (Category.op cat) ≡ cat
cancelDoubleDual {O = O} {_⇒_ = _⇒_} (category _∘_ id assoc cancelLeft cancelRight) =
  cong
    (λ (assoc′ : ∀ {a b c d} (h : c ⇒ d) (g : b ⇒ c) (f : a ⇒ b) → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f)
      → category _∘_ id assoc′ cancelLeft cancelRight)
    (ext-implicit λ _ → ext-implicit λ _ → ext-implicit λ _ → ext-implicit λ _ → ext λ _ → ext λ _ → ext λ _ → K)

