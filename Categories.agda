module Categories where

open import Data.Fin
open import Data.Product hiding (map)
open import Function hiding (_∘_; id)
open import Level using (Level; _⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open ≡-Reasoning

record Category {ℓ₁ ℓ₂} (O : Set ℓ₁) (_⇒_ : O → O → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
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

module Structures {ℓ₁ ℓ₂} {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂} (cat : Category O _⇒_)  where
  open Category cat

  record InitialObject ⊥ : Set (ℓ₁ ⊔ ℓ₂) where
    field
      initial : ∀ {x} → ⊥ ⇒ x
      uniqueness : ∀ {x} {m : ⊥ ⇒ x} → m ≡ initial

  record TerminalObject ⊤ : Set (ℓ₁ ⊔ ℓ₂) where
    field
      terminal : ∀ {x} → x ⇒ ⊤
      uniqueness : ∀ {x} {m : x ⇒ ⊤} → m ≡ terminal

  record Product a b c : Set (ℓ₁ ⊔ ℓ₂) where
    field
      fst : c ⇒ a
      snd : c ⇒ b

  record UniversalProduct a b c : Set (ℓ₁ ⊔ ℓ₂) where
    open Product {{...}}

    field
      product : Product a b c
      factor : ∀ {c′} → (p : c′ ⇒ a) → (q : c′ ⇒ b) → ∃ λ m → (p ≡ fst ∘ m) × (q ≡ snd ∘ m)

  record Coproduct a b c : Set (ℓ₁ ⊔ ℓ₂) where
    field
      left : a ⇒ c
      right : b ⇒ c

  record UniversalCoproduct a b c : Set (ℓ₁ ⊔ ℓ₂) where
    open Coproduct {{...}}

    field
      coproduct : Coproduct a b c
      factor : ∀ {c′} → (p : a ⇒ c′) → (q : b ⇒ c′) → ∃ λ m → (p ≡ m ∘ left) × (q ≡ m ∘ right)

  record Endofunctor (F : O → O) : Set (ℓ₁ ⊔ ℓ₂) where
    field
      map : ∀ {a b} → (a ⇒ b) → (F a ⇒ F b)
      map-id : ∀ {a} → map (id {a}) ≡ id
      map-∘ : ∀ {a b c} → (f : a ⇒ b) → (g : b ⇒ c) → map (g ∘ f) ≡ map g ∘ map f

  module Endobifunctor where
    open Endofunctor {{...}}

    record FromEndofunctors (F : O → O → O) : Set (ℓ₁ ⊔ ℓ₂) where
      field
        endofunctorᴸ : ∀ {b} → Endofunctor (λ a → F a b)
        endofunctorᴿ : ∀ {a} → Endofunctor (λ b → F a b)
        mapCommutes : ∀ {a b c d} {f : a ⇒ b} {g : c ⇒ d} → map {{endofunctorᴸ}} f ∘ map g ≡ map g ∘ map f

record Functor {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᶠ : Set ℓ₃}
    {_⇒_ : O → O → Set ℓ₂} {_⇒ᶠ_ : Oᶠ → Oᶠ → Set ℓ₄}
    (cat : Category O _⇒_) (catᶠ : Category Oᶠ _⇒ᶠ_) 
    (F : O → Oᶠ)
    : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where

  open Category cat
  open Category catᶠ renaming (id to idᶠ; _∘_ to _∘ᶠ_)

  field
    map : ∀ {a b} → (a ⇒ b) → (F a ⇒ᶠ F b)
    map-id : ∀ {a} → map (id {a}) ≡ idᶠ
    map-∘ : ∀ {a b c} → (f : a ⇒ b) → (g : b ⇒ c) → map (g ∘ f) ≡ map g ∘ᶠ map f

-- constant functor
Δ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {Oᶠ : Set ℓ₃}
  {_⇒_ : O → O → Set ℓ₂} {_⇒ᶠ_ : Oᶠ → Oᶠ → Set ℓ₄}
  (cat : Category O _⇒_) (catᶠ : Category Oᶠ _⇒ᶠ_)
  (c : Oᶠ) →
  Functor cat catᶠ (const c)
Δ cat catᶠ c = record
  { map = const id
  ; map-id = refl
  ; map-∘ = const (const (sym cancelLeft))
  }
  where
    open Category {{...}}

module Bifunctor where
  open Functor {{...}}
  open Category {{...}}

  record FromFunctors {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
      {Oᴸ : Set ℓ₁} {Oᴿ : Set ℓ₂} {Oᶠ : Set ℓ₃}
      {_⇒ᴸ_ : Oᴸ → Oᴸ → Set ℓ₄} {_⇒ᴿ_ : Oᴿ → Oᴿ → Set ℓ₅} {_⇒ᶠ_ : Oᶠ → Oᶠ → Set ℓ₆}
      (catᴸ : Category Oᴸ _⇒ᴸ_) (catᴿ : Category Oᴿ _⇒ᴿ_) (catᶠ : Category Oᶠ _⇒ᶠ_)
      (F : Oᴸ → Oᴿ → Oᶠ)
      : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where

    field
      functorᴸ : ∀ {b} → Functor catᴸ catᶠ (λ a → F a b)
      functorᴿ : ∀ {a} → Functor catᴿ catᶠ (λ b → F a b)

    -- there might be a less redundant way to do this - instance search doesn't look at fields
    instance functorL : ∀ {b} → Functor catᴸ catᶠ (λ a → F a b)
    functorL = functorᴸ

    instance functorR : ∀ {a} → Functor catᴿ catᶠ (λ b → F a b)
    functorR = functorᴿ

    field
      mapCommutes : ∀ {a b c d} {f : a ⇒ᴸ b} {g : c ⇒ᴿ d} → map f ∘ map g ≡ map g ∘ map f

    bimap : ∀ {a b c d} → (a ⇒ᴸ b) → (c ⇒ᴿ d) → (F a c ⇒ᶠ F b d)
    bimap f g = map f ∘ map g

    bimap-id : ∀ {a : Oᴸ} {b : Oᴿ} → bimap (id {a = a}) (id {a = b}) ≡ id
    bimap-id {a} {b} = trans (cong-∘ map-id map-id) cancelLeft

    bimap-∘ : ∀ {a b c x y z} → (f : a ⇒ᴸ b) → (g : b ⇒ᴸ c) → (h : x ⇒ᴿ y) → (i : y ⇒ᴿ z) → bimap (g ∘ f) (i ∘ h) ≡ bimap g i ∘ bimap f h
    bimap-∘ f g h i =
      -- this might be cleaner taken from the other angle
      begin
        map (g ∘ f) ∘ map (i ∘ h)
      ≡⟨ cong-∘ (map-∘ f g) (map-∘ h i) ⟩
        (map g ∘ map f) ∘ (map i ∘ map h)
      ≡⟨ assoc _ _ _ ⟩
        ((map g ∘ map f) ∘ map i) ∘ map h
      ≡⟨ cong-∘ᴸ (sym (assoc _ _ _)) ⟩
        (map g ∘ (map f ∘ map i)) ∘ map h
      ≡⟨ cong-∘ᴸ (cong-∘ᴿ mapCommutes) ⟩
        (map g ∘ (map i ∘ map f)) ∘ map h
      ≡⟨ cong-∘ᴸ (assoc _ _ _) ⟩
        ((map g ∘ map i) ∘ map f) ∘ map h
      ≡⟨ sym (assoc _ _ _) ⟩
        (map g ∘ map i) ∘ (map f ∘ map h)
      ∎

  record FromBimap {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
      {Oᴸ : Set ℓ₁} {Oᴿ : Set ℓ₂} {Oᶠ : Set ℓ₃}
      {_⇒ᴸ_ : Oᴸ → Oᴸ → Set ℓ₄} {_⇒ᴿ_ : Oᴿ → Oᴿ → Set ℓ₅} {_⇒ᶠ_ : Oᶠ → Oᶠ → Set ℓ₆}
      (catᴸ : Category Oᴸ _⇒ᴸ_) (catᴿ : Category Oᴿ _⇒ᴿ_) (catᶠ : Category Oᶠ _⇒ᶠ_)
      (F : Oᴸ → Oᴿ → Oᶠ)
      : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where

    field
      bimap : ∀ {a b c d} → (a ⇒ᴸ b) → (c ⇒ᴿ d) → (F a c ⇒ᶠ F b d)
      bimap-id : {a : Oᴸ} {b : Oᴿ} → bimap (id {a = a}) (id {a = b}) ≡ id
      bimap-∘ : ∀
        {a b c x y z}
        (f : a ⇒ᴸ b) (g : b ⇒ᴸ c)
        (h : x ⇒ᴿ y) (i : y ⇒ᴿ z)
        →
        bimap (g ∘ f) (i ∘ h) ≡ bimap g i ∘ bimap f h

    functorᴸ : ∀ {b} → Functor catᴸ catᶠ (λ a → F a b)
    functorᴸ = record
      { map = λ f → bimap f id
      ; map-id = bimap-id
      ; map-∘ = λ f g →
          begin
            bimap (g ∘ f) id
          ≡⟨ cong (bimap (g ∘ f)) (sym cancelLeft) ⟩
            bimap (g ∘ f) (id ∘ id)
          ≡⟨ bimap-∘ f g id id ⟩
            bimap g id ∘ bimap f id
          ∎
      }

    functorᴿ : ∀ {a} → Functor catᴿ catᶠ (λ b → F a b)
    functorᴿ = record
      { map = λ f → bimap id f
      ; map-id = bimap-id
      ; map-∘ = λ f g →
          begin
            bimap id (g ∘ f)
          ≡⟨ cong (flip bimap (g ∘ f)) (sym cancelLeft) ⟩
            bimap (id ∘ id) (g ∘ f)
          ≡⟨ bimap-∘ id id f g ⟩
            bimap id g ∘ bimap id f
          ∎
      }

record NaturalTransformation {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᵅ : Set ℓ₂}
    {_⇒_ : O → O → Set ℓ₃} {_⇒ᵅ_ : Oᵅ → Oᵅ → Set ℓ₄}
    {cat : Category O _⇒_} {catᵅ : Category Oᵅ _⇒ᵅ_}
    {F : O → Oᵅ} {G : O → Oᵅ}
    (functorF : Functor cat catᵅ F) (functorG : Functor cat catᵅ G)
    : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Category {{...}}
  open Functor functorF renaming (map to mapᶠ)
  open Functor functorG renaming (map to mapᵍ)

  field
    α : ∀ a → F a ⇒ᵅ G a
    naturality : ∀ {a b} (f : a ⇒ b) → α b ∘ mapᶠ f ≡ mapᵍ f ∘ α a

record Cone {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᴵ : Set ℓ₂}
    {_⇒_ : O → O → Set ℓ₃} {_⇒ᴵ_ : Oᴵ → Oᴵ → Set ℓ₄}
    {cat : Category O _⇒_} {catᴵ : Category Oᴵ _⇒ᴵ_}
    {D : Oᴵ → O}
    (functorD : Functor catᴵ cat D)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Category {{...}}
  open NaturalTransformation {{...}}

  field
    apex : O
    naturalTransformation : NaturalTransformation (Δ catᴵ cat apex) functorD

-- aka universal cone
record Limit
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᴵ : Set ℓ₂}
    {_⇒_ : O → O → Set ℓ₃} {_⇒ᴵ_ : Oᴵ → Oᴵ → Set ℓ₄}
    {cat : Category O _⇒_} {catᴵ : Category Oᴵ _⇒ᴵ_}
    {D : Oᴵ → O}
    (functorD : Functor catᴵ cat D)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Category {{...}}

  field
    cone : Cone functorD

  open Cone cone
  open NaturalTransformation naturalTransformation

  field
    factor :
      {apex′ : O}
      (nt : NaturalTransformation (Δ catᴵ cat apex′) functorD)
      (a : Oᴵ)
      →
      let β = NaturalTransformation.α nt in Σ[ m ∈ apex′ ⇒ apex ] (β a ≡ α a ∘ m)

module Equalizer where
  open import Data.Product using (_,_)

  open Structures {{...}}
  open Category {{...}}

  data I : Set where aᴵ bᴵ : I

  data _⇒ᴵ_ : I → I → Set where
    idᴵ : ∀ {a} → a ⇒ᴵ a
    fᴵ gᴵ : aᴵ ⇒ᴵ bᴵ

  _∘ᴵ_ : ∀ {a b c} → (b ⇒ᴵ c) → (a ⇒ᴵ b) → (a ⇒ᴵ c)
  idᴵ ∘ᴵ idᴵ = idᴵ
  idᴵ ∘ᴵ fᴵ = fᴵ
  idᴵ ∘ᴵ gᴵ = gᴵ
  fᴵ ∘ᴵ idᴵ = fᴵ
  gᴵ ∘ᴵ idᴵ = gᴵ

  cancelLeftᴵ : ∀ {a b} {f : a ⇒ᴵ b} → idᴵ ∘ᴵ f ≡ f
  cancelLeftᴵ {f = idᴵ} = refl
  cancelLeftᴵ {f = fᴵ} = refl
  cancelLeftᴵ {f = gᴵ} = refl

  cancelRightᴵ : ∀ {a b} {f : a ⇒ᴵ b} → f ∘ᴵ idᴵ ≡ f
  cancelRightᴵ {f = idᴵ} = refl
  cancelRightᴵ {f = fᴵ} = refl
  cancelRightᴵ {f = gᴵ} = refl
  
  assocᴵ : ∀ {a b c d} (h : c ⇒ᴵ d) (g : b ⇒ᴵ c) (f : a ⇒ᴵ b) → h ∘ᴵ (g ∘ᴵ f) ≡ (h ∘ᴵ g) ∘ᴵ f
  assocᴵ idᴵ idᴵ idᴵ = refl
  assocᴵ idᴵ idᴵ fᴵ = refl
  assocᴵ idᴵ idᴵ gᴵ = refl
  assocᴵ idᴵ fᴵ idᴵ = refl
  assocᴵ idᴵ gᴵ idᴵ = refl
  assocᴵ fᴵ idᴵ idᴵ = refl
  assocᴵ gᴵ idᴵ idᴵ = refl

  instance
    categoryI : Category I _⇒ᴵ_
    categoryI = record
      { _∘_ = _∘ᴵ_
      ; id = idᴵ
      ; assoc = assocᴵ
      ; cancelLeft = cancelLeftᴵ
      ; cancelRight = cancelRightᴵ
      }

  D : ∀ {ℓ} {O : Set ℓ} → O → O → I → O
  D a _ aᴵ = a
  D _ b bᴵ = b

  instance
    functorD : ∀ {ℓ₁ ℓ₂}
      {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
      {a b : O}
      (cat : Category O _⇒_)
      (f g : a ⇒ b)
      →
      Functor categoryI cat (D a b)
    functorD cat  f g = record
      { map = λ
        { {aᴵ} idᴵ → id
        ; {bᴵ} idᴵ → id
        ; fᴵ → f
        ; gᴵ → g
        }
      ; map-id = λ
        { {aᴵ} → refl
        ; {bᴵ} → refl
        }
      ; map-∘ = λ
        { {aᴵ} idᴵ idᴵ → sym cancelRight
        ; {aᴵ} idᴵ fᴵ → sym cancelRight
        ; {aᴵ} idᴵ gᴵ → sym cancelRight
        ; {bᴵ} idᴵ idᴵ → sym cancelRight
        ; fᴵ idᴵ → sym cancelLeft
        ; gᴵ idᴵ → sym cancelLeft
        }
      }

  Equalizer : ∀
    {ℓ₁ ℓ₂}
    {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
    {a b : O}
    (cat : Category O _⇒_)
    (f g : a ⇒ b)
    →
    Set (ℓ₁ ⊔ ℓ₂)
  Equalizer cat f g = Limit (functorD cat f g)