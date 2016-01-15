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
  HomSet a b = a ⇒ b

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

record Functor
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᶠ : Set ℓ₃}
    {_⇒_ : O → O → Set ℓ₂} {_⇒ᶠ_ : Oᶠ → Oᶠ → Set ℓ₄}
    (cat : Category O _⇒_) (catᶠ : Category Oᶠ _⇒ᶠ_) 
    (F : O → Oᶠ)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where

  open Category cat
  open Category catᶠ renaming (id to idᶠ; _∘_ to _∘ᶠ_)

  field
    map : ∀ {a b} → (a ⇒ b) → (F a ⇒ᶠ F b)
    map-id : ∀ {a} → map (id {a}) ≡ idᶠ
    map-∘ : ∀ {a b c} → (f : a ⇒ b) → (g : b ⇒ c) → map (g ∘ f) ≡ map g ∘ᶠ map f

Endofunctor : ∀
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  (F : O → O)
  →
  Set (ℓ₁ ⊔ ℓ₂)
Endofunctor cat F = Functor cat cat F

-- constant functor
Δ : ∀
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {Oᶠ : Set ℓ₃}
  {_⇒_ : O → O → Set ℓ₂} {_⇒ᶠ_ : Oᶠ → Oᶠ → Set ℓ₄}
  (cat : Category O _⇒_) (catᶠ : Category Oᶠ _⇒ᶠ_)
  (c : Oᶠ)
  →
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

  record FromFunctors
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
    {Oᴸ : Set ℓ₁} {Oᴿ : Set ℓ₂} {Oᶠ : Set ℓ₃}
    {_⇒ᴸ_ : Oᴸ → Oᴸ → Set ℓ₄} {_⇒ᴿ_ : Oᴿ → Oᴿ → Set ℓ₅} {_⇒ᶠ_ : Oᶠ → Oᶠ → Set ℓ₆}
    (catᴸ : Category Oᴸ _⇒ᴸ_) (catᴿ : Category Oᴿ _⇒ᴿ_) (catᶠ : Category Oᶠ _⇒ᶠ_)
    (F : Oᴸ → Oᴿ → Oᶠ)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where

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

    bimap-∘ : ∀
      {a b c x y z}
      (f : a ⇒ᴸ b)
      (g : b ⇒ᴸ c)
      (h : x ⇒ᴿ y)
      (i : y ⇒ᴿ z)
      →
      bimap (g ∘ f) (i ∘ h) ≡ bimap g i ∘ bimap f h
    bimap-∘ f g h i =
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

  record FromBimap
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
    {Oᴸ : Set ℓ₁} {Oᴿ : Set ℓ₂} {Oᶠ : Set ℓ₃}
    {_⇒ᴸ_ : Oᴸ → Oᴸ → Set ℓ₄} {_⇒ᴿ_ : Oᴿ → Oᴿ → Set ℓ₅} {_⇒ᶠ_ : Oᶠ → Oᶠ → Set ℓ₆}
    (catᴸ : Category Oᴸ _⇒ᴸ_) (catᴿ : Category Oᴿ _⇒ᴿ_) (catᶠ : Category Oᶠ _⇒ᶠ_)
    (F : Oᴸ → Oᴿ → Oᶠ)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where

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

module Endobifunctor where
  FromEndofunctors : ∀
    {ℓ₁ ℓ₂}
    {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
    (cat : Category O _⇒_)
    (F : O → O → O)
    →
    Set (ℓ₁ ⊔ ℓ₂)
  FromEndofunctors cat F = Bifunctor.FromFunctors cat cat cat F

  FromBimap : ∀
    {ℓ₁ ℓ₂}
    {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
    (cat : Category O _⇒_)
    (F : O → O → O)
    →
    Set (ℓ₁ ⊔ ℓ₂)
  FromBimap cat F = Bifunctor.FromBimap cat cat cat F

record NaturalTransformation
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᵅ : Set ℓ₂}
    {_⇒_ : O → O → Set ℓ₃} {_⇒ᵅ_ : Oᵅ → Oᵅ → Set ℓ₄}
    {cat : Category O _⇒_} {catᵅ : Category Oᵅ _⇒ᵅ_}
    {F : O → Oᵅ} {G : O → Oᵅ}
    (functorF : Functor cat catᵅ F) (functorG : Functor cat catᵅ G)
    (α : ∀ a → F a ⇒ᵅ G a)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Category {{...}}
  open Functor functorF renaming (map to mapᶠ)
  open Functor functorG renaming (map to mapᵍ)

  field
    naturality : ∀ {a b} (f : a ⇒ b) → α b ∘ mapᶠ f ≡ mapᵍ f ∘ α a

record NaturalIsomorphism
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {O′ : Set ℓ₂}
    {_⇒_ : O → O → Set ℓ₃} {_⇒′_ : O′ → O′ → Set ℓ₄}
    {cat : Category O _⇒_} {cat′ : Category O′ _⇒′_}
    {F : O → O′} {G : O → O′}
    (functorF : Functor cat cat′ F) (functorG : Functor cat cat′ G)
    (α : ∀ a → F a ⇒′ G a)
    (β : ∀ a → G a ⇒′ F a)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Category cat′

  field
    right : NaturalTransformation functorF functorG α
    left : NaturalTransformation functorG functorF β
    leftId : ∀ x → α x ∘ β x ≡ id
    rightId : ∀ x → β x ∘ α x ≡ id

record Cone
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᴵ : Set ℓ₂}
    {_⇒_ : O → O → Set ℓ₃} {_⇒ᴵ_ : Oᴵ → Oᴵ → Set ℓ₄}
    {cat : Category O _⇒_} {catᴵ : Category Oᴵ _⇒ᴵ_}
    {D : Oᴵ → O}
    (functorD : Functor catᴵ cat D)
    (apex : O)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Category {{...}}
  open NaturalTransformation {{...}}

  field
    α : ∀ a → const apex a ⇒ D a
    naturalTransformation : NaturalTransformation (Δ catᴵ cat apex) functorD α

record Cocone
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᴵ : Set ℓ₂}
    {_⇒_ : O → O → Set ℓ₃} {_⇒ᴵ_ : Oᴵ → Oᴵ → Set ℓ₄}
    {cat : Category O _⇒_} {catᴵ : Category Oᴵ _⇒ᴵ_}
    {D : Oᴵ → O}
    (functorD : Functor catᴵ cat D)
    (apex : O) -- coapex?
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  open Category {{...}}
  open NaturalTransformation {{...}}

  field
    α : ∀ a → D a ⇒ const apex a
    naturalTransformation : NaturalTransformation functorD (Δ catᴵ cat apex) α

-- aka universal cone
record Limit
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᴵ : Set ℓ₂}
    {_⇒_ : O → O → Set ℓ₃} {_⇒ᴵ_ : Oᴵ → Oᴵ → Set ℓ₄}
    {cat : Category O _⇒_} {catᴵ : Category Oᴵ _⇒ᴵ_}
    {D : Oᴵ → O}
    (functorD : Functor catᴵ cat D)
    (apex : O)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    cone : Cone functorD apex

  open Category cat
  open Cone cone

  field
    factor :
      {c : O}
      (β : ∀ a → const c a ⇒ D a)
      (nt : NaturalTransformation (Δ catᴵ cat c) functorD β)
      →
      Σ[ m ∈ c ⇒ apex ] (∀ a → β a ≡ α a ∘ m)

record Colimit
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {O : Set ℓ₁} {Oᴵ : Set ℓ₂}
    {_⇒_ : O → O → Set ℓ₃} {_⇒ᴵ_ : Oᴵ → Oᴵ → Set ℓ₄}
    {cat : Category O _⇒_} {catᴵ : Category Oᴵ _⇒ᴵ_}
    {D : Oᴵ → O}
    (functorD : Functor catᴵ cat D)
    (apex : O)
    :
    Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    cocone : Cocone functorD apex

  open Category cat
  open Cocone cocone

  field
    factor :
      {c : O}
      (β : ∀ a → D a ⇒ const c a)
      (nt : NaturalTransformation functorD (Δ catᴵ cat c) β)
      (a : Oᴵ)
      →
      ∃ λ m → β a ≡ m ∘ α a

module Equalizer
    {ℓ₁ ℓ₂}
    {O : Set ℓ₁}
    {_⇒_ : O → O → Set ℓ₂}
    (cat : Category O _⇒_)
    {a b : O}
    (f g : a ⇒ b) where
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
    catᴵ : Category I _⇒ᴵ_
    catᴵ = record
      { _∘_ = _∘ᴵ_
      ; id = idᴵ
      ; assoc = assocᴵ
      ; cancelLeft = cancelLeftᴵ
      ; cancelRight = cancelRightᴵ
      }

  D : I → O
  D aᴵ = a
  D bᴵ = b

  instance
    functorD : Functor catᴵ cat D
    functorD = record
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

  Equalizer : O → Set (ℓ₁ ⊔ ℓ₂)
  Equalizer apex = Limit functorD apex

module Pullback
    {ℓ₁ ℓ₂}
    {O : Set ℓ₁}
    {_⇒_ : O → O → Set ℓ₂}
    (cat : Category O _⇒_)
    {a b c : O}
    (f : a ⇒ b)
    (g : c ⇒ b) where
  open import Data.Product using (_,_)
  open Category cat

  data I : Set where aᴵ bᴵ cᴵ : I

  -- "this diagram is often called a span"
  data _⇒ᴵ_ : I → I → Set where
    idᴵ : ∀ {x} → x ⇒ᴵ x
    fᴵ : aᴵ ⇒ᴵ bᴵ
    gᴵ : cᴵ ⇒ᴵ bᴵ

  _∘ᴵ_ : ∀ {x y z} → (y ⇒ᴵ z) → (x ⇒ᴵ y) → (x ⇒ᴵ z)
  h ∘ᴵ idᴵ = h
  idᴵ ∘ᴵ h = h

  instance
    catᴵ : Category I _⇒ᴵ_
    catᴵ = record
      { _∘_ = _∘ᴵ_
      ; id = idᴵ
      ; assoc = λ
          { {aᴵ} h g idᴵ → refl
          ; {bᴵ} h g idᴵ → refl
          ; {cᴵ} h g idᴵ → refl
          ; h idᴵ fᴵ → refl
          ; h idᴵ gᴵ → refl
          }
      ; cancelLeft = λ
          { {f = idᴵ} → refl
          ; {f = fᴵ} → refl
          ; {f = gᴵ} → refl
          }
      ; cancelRight = λ
          { {f = idᴵ} → refl
          ; {f = fᴵ} → refl
          ; {f = gᴵ} → refl
          }
      }

  D : I → O
  D aᴵ = a
  D bᴵ = b
  D cᴵ = c

  instance
    functorD : Functor catᴵ cat D
    functorD = record
      { map = λ
          { {aᴵ} idᴵ → id
          ; {bᴵ} idᴵ → id
          ; {cᴵ} idᴵ → id
          ; fᴵ → f
          ; gᴵ → g
          }
      ; map-id = λ { {aᴵ} → refl ; {bᴵ} → refl ; {cᴵ} → refl }
      ; map-∘ = λ
          { {aᴵ} idᴵ idᴵ → sym cancelLeft
          ; {bᴵ} idᴵ idᴵ → sym cancelLeft
          ; {cᴵ} idᴵ idᴵ → sym cancelLeft
          ; idᴵ fᴵ → sym cancelRight
          ; idᴵ gᴵ → sym cancelRight
          ; fᴵ idᴵ → sym cancelLeft
          ; gᴵ idᴵ → sym cancelLeft
          }
      }

  Pullback : O → Set (ℓ₁ ⊔ ℓ₂)
  Pullback apex = Limit functorD apex

module Pushout
    {ℓ₁ ℓ₂}
    {O : Set ℓ₁}
    {_⇒_ : O → O → Set ℓ₂}
    (cat : Category O _⇒_)
    {a b c : O}
    (f : b ⇒ a)
    (g : b ⇒ c) where
  open Pullback (Category.op cat) f g

  Pushout : O → Set (ℓ₁ ⊔ ℓ₂)
  Pushout = Pullback
