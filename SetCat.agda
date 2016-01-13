module SetCat where

open import Data.Product using (_,_; _,′_; _×_)
open import Level
open import Relation.Binary.PropositionalEquality

open import Axioms
open import Categories

infixr 1 _⇒_
_⇒_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
a ⇒ b = a → b

instance
  setCategory : ∀ ℓ → Category (Set ℓ) _⇒_
  setCategory _ = record
      { _∘_ = λ g f x → g (f x)
      ; id = λ x → x
      ; assoc = λ _ _ _ → ext λ _ → refl
      ; cancelLeft = ext λ _ → refl
      ; cancelRight = ext λ _ → refl
      }

module ⊥-InitialObject where
    open import Data.Empty
    open Category (setCategory zero)
    open Structures (setCategory zero)
    instance
      ⊥-initial : InitialObject ⊥
      ⊥-initial = record
        { initial = ⊥-elim
        ; uniqueness = ext λ ()
        }

module ⊤-TerminalObject where
  open import Data.Unit
  open Category (setCategory zero)
  open Structures (setCategory zero)
  instance
    ⊤-terminal : TerminalObject ⊤
    ⊤-terminal = record
      { terminal = λ _ → tt
      ; uniqueness = ext λ _ → refl
      }

module ×-Product ℓ where
  open import Data.Product
  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)

  instance
    ×-product : ∀ {a b} → Product a b (a × b)
    ×-product = record
      { fst = proj₁
      ; snd = proj₂
      }

  instance
    ×-universalProduct : ∀ {a b} → UniversalProduct a b (a × b)
    ×-universalProduct = record
      { product = ×-product
      ; factor = λ p′ q′ → < p′ , q′ > , refl ,′ refl
      }

module ⊎-Coproduct ℓ where
  open import Data.Sum
  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)

  instance
    ⊎-coproduct : ∀ {a b} → Coproduct a b (a ⊎ b)
    ⊎-coproduct = record
      { left = inj₁
      ; right = inj₂
      }

    ⊎-universalCoproduct : ∀ {a b} → UniversalCoproduct a b (a ⊎ b)
    ⊎-universalCoproduct = record
      { coproduct = ⊎-coproduct
      ; factor = λ i′ j′ → [ i′ , j′ ]′ , refl ,′ refl
      }

module MaybeEndofunctor ℓ where
  open import Data.Maybe
  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)

  map-id : ∀ {a} (x : Maybe a) → map id x ≡ id x
  map-id (just x) = refl
  map-id nothing = refl

  map-∘ : ∀ {a b c} (f : a ⇒ b) (g : b ⇒ c) (x : Maybe a) → map (g ∘ f) x ≡ (map g ∘ map f) x
  map-∘ f g (just x) = refl
  map-∘ f g nothing = refl

  instance
    MaybeEndofunctor : Endofunctor (setCategory ℓ) Maybe
    MaybeEndofunctor = record
      { map = map
      ; map-id = ext map-id
      ; map-∘ = λ f g → ext (map-∘ f g)
      }

module ListEndofunctor ℓ where
  open import Data.List
  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)

  map-id : ∀ {a} (x : List a) → map id x ≡ id x
  map-id [] = refl
  map-id (x ∷ xs) rewrite map-id xs = refl

  map-∘ : ∀ {a b c} (f : a ⇒ b) (g : b ⇒ c) (x : List a) → map (g ∘ f) x ≡ (map g ∘ map f) x
  map-∘ f g [] = refl
  map-∘ f g (x ∷ xs) rewrite map-∘ f g xs = refl

  instance
    ListEndofunctor : Endofunctor (setCategory ℓ) List
    ListEndofunctor = record
      { map = map
      ; map-id = ext map-id
      ; map-∘ = λ f g → ext (map-∘ f g)
      }

module ReaderEndofunctor ℓ where
  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)

  instance
    ReaderEndofunctor : (a : Set ℓ) → Endofunctor (setCategory ℓ) (λ b → (a ⇒ b))
    ReaderEndofunctor a = record
      { map = _∘_
      ; map-id = refl
      ; map-∘ = λ _ _ → refl
      }

module ×-Endobifunctor ℓ where
  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)

  instance
    ×-Endofunctorᴸ : {b : Set ℓ} → Endofunctor (setCategory ℓ) (λ a → a × b)
    ×-Endofunctorᴸ = record
      { map = λ { f (x , y) → f x , y }
      ; map-id = refl
      ; map-∘ = λ _ _ → refl
      }

  instance
    ×-Endofunctorᴿ : {a : Set ℓ} → Endofunctor (setCategory ℓ) (λ b → a × b)
    ×-Endofunctorᴿ = record
      { map = λ { f (x , y) → x , f y }
      ; map-id = refl
      ; map-∘ = λ _ _ → refl
      }

  instance
    ×-Endobifunctor : Endobifunctor.FromEndofunctors (setCategory ℓ) _×_
    ×-Endobifunctor = record
      { functorᴸ = ×-Endofunctorᴸ
      ; functorᴿ = ×-Endofunctorᴿ
      ; mapCommutes = ext λ _ → refl
      }

module ⊎-Endobifunctor ℓ where
  open import Data.Sum
  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)

  instance
    ⊎-Endofunctorᴸ : {b : Set ℓ} → Endofunctor (setCategory ℓ) (λ a → a ⊎ b)
    ⊎-Endofunctorᴸ = record
      { map = λ { f (inj₁ x) → inj₁ (f x); f (inj₂ y) → inj₂ y }
      ; map-id = ext λ { (inj₁ _) → refl; (inj₂ _) → refl }
      ; map-∘ = λ _ _ → ext λ { (inj₁ _) → refl; (inj₂ _) → refl }
      }

  instance
    ⊎-Endofunctorᴿ : {a : Set ℓ} → Endofunctor (setCategory ℓ) (λ b → a ⊎ b)
    ⊎-Endofunctorᴿ = record
      { map = λ { f (inj₁ x) → inj₁ x; f (inj₂ y) → inj₂ (f y) }
      ; map-id = ext λ { (inj₁ _) → refl; (inj₂ _) → refl }
      ; map-∘ = λ _ _ → ext λ { (inj₁ _) → refl; (inj₂ _) → refl }
      }

  instance
    ⊎-Endobifunctor : Endobifunctor.FromEndofunctors (setCategory ℓ) _⊎_
    ⊎-Endobifunctor = record
      { functorᴸ = ⊎-Endofunctorᴸ
      ; functorᴿ = ⊎-Endofunctorᴿ
      ; mapCommutes = ext λ { (inj₁ _) → refl ; (inj₂ _) → refl }
      }

module DependentPairEqualizer {ℓ} {a b : Set ℓ} (f g : a ⇒ b) where
  open import Data.Product using (∃; _,_; proj₁; proj₂)
  open import Function using (const)
  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)
  open Equalizer (setCategory ℓ) f g renaming (Equalizer to Equalizerᶠᵍ)

  DepEq : Set ℓ
  DepEq = ∃ λ x → f x ≡ g x

  open Functor (Δ catᴵ (setCategory ℓ) DepEq) renaming (map to mapᵟ)
  open Functor functorD

  α : ∀ x → const DepEq x ⇒ D x
  α {aᴵ} = proj₁
  α {bᴵ} = f ∘ proj₁

  naturality : ∀ {a b} (f : a ⇒ᴵ b) → α b ∘ mapᵟ f ≡ map f ∘ α a
  naturality {aᴵ} idᴵ = refl
  naturality {bᴵ} idᴵ = refl
  naturality fᴵ = refl
  naturality gᴵ = ext proj₂
  
  factor : ∀
   {c}
   (β : ∀ x → const c x ⇒ D x)
   (nt : NaturalTransformation (Δ catᴵ (setCategory ℓ) c) functorD β)
   →
   ∃ λ m → (∀ a → β a ≡ α a ∘ m)
  factor β nt = (λ x → β aᴵ x , trans (sym (naturalityᵝ fᴵ $$ x)) (naturalityᵝ gᴵ $$ x)) , λ
    { aᴵ → refl
    ; bᴵ → naturalityᵝ fᴵ
    }
    where open NaturalTransformation nt renaming (naturality to naturalityᵝ)

  instance
    DepEq-Equalizer : Equalizerᶠᵍ DepEq
    DepEq-Equalizer = record
      { cone = record { naturalTransformation = record { naturality = naturality } }
      ; factor = factor
      }

module ProductPullback {ℓ} {a b c : Set ℓ} (f : a → b) (g : c → b) where
  open import Data.Product using (∃; _,_; proj₁; proj₂)
  open import Function using (const)
  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)
  open Pullback (setCategory ℓ) f g renaming (Pullback to Pullbackᶠᵍ)

  ProdEq : Set ℓ
  ProdEq = ∃ λ x → f (proj₁ x) ≡ g (proj₂ x)

  open Functor (Δ catᴵ (setCategory ℓ) ProdEq) renaming (map to mapᵟ)
  open Functor functorD

  α : ∀ x → const ProdEq x ⇒ D x
  α aᴵ = proj₁ ∘ proj₁
  α bᴵ = f ∘ proj₁ ∘ proj₁
  α cᴵ = proj₂ ∘ proj₁

  naturality : ∀ {a b} (h : a ⇒ᴵ b) → α b ∘ mapᵟ h ≡ map h ∘ α a
  naturality {aᴵ} idᴵ = refl
  naturality {bᴵ} idᴵ = refl
  naturality {cᴵ} idᴵ = refl
  naturality fᴵ = refl
  naturality gᴵ = ext proj₂
  
  factor : ∀
    {c}
    (β : ∀ x → const c x ⇒ D x)
    (nt : NaturalTransformation (Δ catᴵ (setCategory ℓ) c) functorD β)
    →
    ∃ λ m → (∀ a → β a ≡ α a ∘ m)
  factor β nt = (λ x → (((β aᴵ x) , (β cᴵ x)) , trans (sym (naturalityᵝ fᴵ $$ x)) (naturalityᵝ gᴵ $$ x))) , λ
    { aᴵ → refl
    ; bᴵ → naturalityᵝ fᴵ
    ; cᴵ → refl
    }
    where open NaturalTransformation nt renaming (naturality to naturalityᵝ)

  instance
    ProdEq-Pullback : Pullbackᶠᵍ ProdEq
    ProdEq-Pullback = record
      { cone = record { naturalTransformation = record { naturality = naturality } }
      ; factor = factor
      }
