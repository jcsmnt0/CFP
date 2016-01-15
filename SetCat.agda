module SetCat where

open import Data.Nat hiding (_⊔_)
open import Data.Product using (_,_; _,′_; _×_)
open import Level using (_⊔_)
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
    open Category (setCategory Level.zero)
    open Structures (setCategory Level.zero)
    instance
      ⊥-initial : InitialObject ⊥
      ⊥-initial = record
        { initial = ⊥-elim
        ; uniqueness = ext λ ()
        }

module ⊤-TerminalObject where
  open import Data.Unit
  open Category (setCategory Level.zero)
  open Structures (setCategory Level.zero)
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

module HomFunctor {ℓ₁ ℓ₂} {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂} (cat : Category O _⇒_) (a : O) where
  open Category cat
  open Structures {{...}}

  instance
    homFunctor : Functor cat (setCategory ℓ₂) (HomSet a)
    homFunctor = record
      { map = _∘_
      ; map-id = ext (λ _ → cancelLeft)
      ; map-∘ = λ _ _ → ext (λ _ → sym (assoc _ _ _))
      }

Representable : ∀
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  {cat : Category O _⇒_}
  {F : O → Set ℓ₂}
  (functorF : Functor cat (setCategory ℓ₂) F)
  {a : O}
  (index : ∀ b → F b → (a ⇒ b))
  (tabulate : ∀ b → (a ⇒ b) → F b)
  →
  Set _
Representable {cat = cat} functorF {a = a} index tabulate = NaturalIsomorphism functorF homFunctor index tabulate
  where
    open HomFunctor cat a

module VecFunctor (n : ℕ) where
  open import Data.Fin
  open import Data.Vec
  open import Function

  map-id : ∀ {ℓ m} {a : Set ℓ} (xs : Vec a m) → map id xs ≡ xs
  map-id [] = refl
  map-id (_ ∷ _) = cong (_∷_ _) (map-id _)

  map-∘ : ∀ {ℓ m} {a b c : Set ℓ} (f : a → b) (g : b → c) (xs : Vec a m) → map (g ∘ f) xs ≡ map g (map f xs)
  map-∘ _ _ [] = refl
  map-∘ _ _ (_ ∷ _) = cong (_∷_ _) (map-∘ _ _ _)

  instance
    vecFunctor : ∀ {ℓ} → Endofunctor (setCategory ℓ) (λ a → Vec a n)
    vecFunctor = record
      { map = map
      ; map-id = ext map-id
      ; map-∘ = λ f g → ext (map-∘ f g)
      }

  mapCommutesOverLookup : ∀
    {ℓ m}
    {a b : Set ℓ}
    {f : a → b}
    (xs : Vec a m)
    (i : Fin m)
    →
    lookup i (map f xs) ≡ f (lookup i xs)
  mapCommutesOverLookup [] ()
  mapCommutesOverLookup (_ ∷ _) zero = refl
  mapCommutesOverLookup (_ ∷ _) (suc i) = mapCommutesOverLookup _ i

  mapCommutesOverTabulate : ∀
    {ℓ m}
    {a b : Set ℓ}
    (f : a → b)
    (tab : Fin m → a)
    →
    tabulate (f ∘ tab) ≡ map f (tabulate tab)
  mapCommutesOverTabulate {m = zero} _ tab = refl
  mapCommutesOverTabulate {m = suc m} f tab = cong (_∷_ (f (tab zero))) (mapCommutesOverTabulate f (tab ∘ suc))

  lookupTabulateCancel : ∀
    {ℓ m}
    {a : Set ℓ}
    (tab : Fin m → a)
    (i : Fin m)
    →
    lookup i (tabulate tab) ≡ tab i
  lookupTabulateCancel tab zero = refl
  lookupTabulateCancel tab (suc i) = lookupTabulateCancel (tab ∘ suc) i

  tabulateLookupCancel : ∀
    {ℓ m}
    {a : Set ℓ}
    (xs : Vec a m)
    →
    tabulate (flip lookup xs) ≡ xs
  tabulateLookupCancel [] = refl
  tabulateLookupCancel (_ ∷ _) = cong (_∷_ _) (tabulateLookupCancel _)

  instance
    vecRepresentable : Representable vecFunctor (λ _ → flip lookup) (λ _ → tabulate)
    vecRepresentable = record
      { right = record
        { naturality = λ _ → ext λ i → ext λ xs → mapCommutesOverLookup i xs
        }
      ; left = record
        { naturality = λ f → ext (mapCommutesOverTabulate f)
        }
      ; leftId = λ _ → ext λ tab → ext (lookupTabulateCancel tab)
      ; rightId = λ _ → ext tabulateLookupCancel
      }
