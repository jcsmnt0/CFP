module Proofs where

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axioms
open import Categories

cancelDoubleDual : ∀
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  → Category.op (Category.op cat) ≡ cat
cancelDoubleDual {O = O} {_⇒_ = _⇒_} (category _∘_ id assoc cancelLeft cancelRight) =
  cong
    (λ (assoc′ : ∀ {a b c d} (h : c ⇒ d) (g : b ⇒ c) (f : a ⇒ b) → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f)
      → category _∘_ id assoc′ cancelLeft cancelRight)
    (ext-implicit λ _ →
      ext-implicit λ _ →
        ext-implicit λ _ →
          ext-implicit λ _ →
            ext λ _ →
              ext λ _ →
                ext λ _ → K)

module Endo {ℓ₁ ℓ₂} {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂} (cat : Category O _⇒_) where
  open Category cat

  module Initial where
    open Structures cat
    open InitialObject {{...}}

    initialObjectUniqueUpToIsomorphism : ∀ {a b} → InitialObject a → InitialObject b → a ⇔ b
    initialObjectUniqueUpToIsomorphism _ _ = record
      { right = initial
      ; left = initial
      ; rightInverse = trans (uniqueness {m = initial ∘ initial}) (sym (uniqueness {m = id}))
      ; leftInverse = trans (uniqueness {m = initial ∘ initial}) (sym (uniqueness {m = id}))
      }

    initialObjectDualOfTerminalObject : ∀ {a} → InitialObject a → Structures.TerminalObject op a
    initialObjectDualOfTerminalObject _ = record
      { terminal = initial
      ; uniqueness = uniqueness
      }

  module Terminal where
    open Structures cat
    open TerminalObject {{...}}

    terminalObjectUniqueUpToIsomorphism : ∀ {a b} → TerminalObject a → TerminalObject b → a ⇔ b
    terminalObjectUniqueUpToIsomorphism _ _ = record
      { right = terminal
      ; left = terminal
      ; rightInverse = trans (uniqueness {m = terminal ∘ terminal}) (sym (uniqueness {m = id}))
      ; leftInverse = trans (uniqueness {m = terminal ∘ terminal}) (sym (uniqueness {m = id}))
      }

    terminalObjectDualOfInitialObject : ∀ {a} → TerminalObject a → Structures.InitialObject op a
    terminalObjectDualOfInitialObject _ = record
      { initial = terminal
      ; uniqueness = uniqueness
      }

  module Product where
    open Structures cat
    open Product {{...}}
    open UniversalProduct {{...}}

    productDualOfCoproduct : ∀ {a b c} → Product a b c → Structures.Coproduct op a b c
    productDualOfCoproduct _ = record
      { left = fst
      ; right = snd
      }

    universalProductDualOfUniversalCoproduct : ∀ {a b c} → UniversalProduct a b c → Structures.UniversalCoproduct op a b c
    universalProductDualOfUniversalCoproduct _ = record
      { coproduct = productDualOfCoproduct product
      ; factor = factor
      }

  module Coproduct where
    open Structures cat
    open Coproduct {{...}}
    open UniversalCoproduct {{...}}

    coproductDualOfProduct : ∀ {a b c} → Coproduct a b c → Structures.Product op a b c
    coproductDualOfProduct _ = record
      { fst = left
      ; snd = right
      }

    universalCoproductDualOfUniversalProduct : ∀ {a b c} → UniversalCoproduct a b c → Structures.UniversalProduct op a b c
    universalCoproductDualOfUniversalProduct _ = record
      { product = coproductDualOfProduct coproduct
      ; factor = factor
      }

  module Endofunctor where
    open Structures cat
    open Endofunctor {{...}}

    endofunctorFunctor : ∀ {F} → Endofunctor F → Functor cat cat F
    endofunctorFunctor _ = record
      { map = map
      ; map-id = map-id
      ; map-∘ = map-∘
      }

  module Endobifunctor where
    open Endofunctor
    open Structures cat
    open Endobifunctor.FromEndofunctors {{...}}

    endobifunctorBifunctor : ∀ {F} → Endobifunctor.FromEndofunctors F → Bifunctor.FromFunctors cat cat cat F 
    endobifunctorBifunctor x = record
      { functorᴸ = endofunctorFunctor endofunctorᴸ
      ; functorᴿ = endofunctorFunctor endofunctorᴿ
      ; mapCommutes = mapCommutes
      }

-- this is why mapCommutes has to be a field of Bifunctor.FromFunctors - it's possible to have a two-place mapping
-- between categories that's functorial in both indices but where the left and right morphism mappings don't commute
module MapDoesn'tAlwaysCommuteBetweenFunctors where
  data Two : Set where u v : Two

  data _⇒²_ : Two → Two → Set where
    id : ∀ {x} → x ⇒² x
    u⇒v : u ⇒² v

  _∘²_ : ∀ {a b c} → b ⇒² c → a ⇒² b → a ⇒² c
  _∘²_ f id = f
  _∘²_ id f = f

  assoc² : ∀ {a b c d} (h : c ⇒² d) (g : b ⇒² c) (f : a ⇒² b) → h ∘² (g ∘² f) ≡ (h ∘² g) ∘² f
  assoc² h g id = refl
  assoc² h id u⇒v = refl

  cancelLeft² : ∀ {a b} {f : a ⇒² b} → id ∘² f ≡ f
  cancelLeft² {f = id} = refl
  cancelLeft² {f = u⇒v} = refl

  cancelRight² : ∀ {a b} {f : a ⇒² b} → f ∘² id ≡ f
  cancelRight² = refl

  instance
    categoryI : Category Two _⇒²_
    categoryI = record
      { _∘_ = _∘²_
      ; id = id
      ; assoc = assoc²
      ; cancelLeft = cancelLeft²
      ; cancelRight = cancelRight²
      }

  data Four : Set where m n o p : Four

  data _⇒⁴_ : Four → Four → Set where
    id : ∀ {x} → x ⇒⁴ x
    m⇒n : m ⇒⁴ n
    m⇒o : m ⇒⁴ o
    m⇒pᴸ : m ⇒⁴ p
    m⇒pᴿ : m ⇒⁴ p
    n⇒p : n ⇒⁴ p
    o⇒p : o ⇒⁴ p

  _∘⁴_ : ∀ {a b c} → b ⇒⁴ c → a ⇒⁴ b → a ⇒⁴ c
  id ∘⁴ f = f
  g ∘⁴ id = g
  n⇒p ∘⁴ m⇒n = m⇒pᴸ
  o⇒p ∘⁴ m⇒o = m⇒pᴿ

  assoc⁴ : ∀ {a b c d} (h : c ⇒⁴ d) (g : b ⇒⁴ c) (f : a ⇒⁴ b) → h ∘⁴ (g ∘⁴ f) ≡ (h ∘⁴ g) ∘⁴ f
  assoc⁴ id g f = refl
  assoc⁴ m⇒n id f = refl
  assoc⁴ m⇒o id f = refl
  assoc⁴ m⇒pᴸ id f = refl
  assoc⁴ m⇒pᴿ id f = refl
  assoc⁴ n⇒p id f = refl
  assoc⁴ o⇒p id f = refl
  assoc⁴ n⇒p m⇒n id = refl
  assoc⁴ o⇒p m⇒o id = refl

  cancelLeft⁴ : ∀ {a b} {f : a ⇒⁴ b} → id ∘⁴ f ≡ f
  cancelLeft⁴ = refl

  cancelRight⁴ : ∀ {a b} {f : a ⇒⁴ b} → f ∘⁴ id ≡ f
  cancelRight⁴ {f = id} = refl
  cancelRight⁴ {f = m⇒n} = refl
  cancelRight⁴ {f = m⇒o} = refl
  cancelRight⁴ {f = m⇒pᴸ} = refl
  cancelRight⁴ {f = m⇒pᴿ} = refl
  cancelRight⁴ {f = n⇒p} = refl
  cancelRight⁴ {f = o⇒p} = refl

  instance
    fourCategory : Category Four _⇒⁴_
    fourCategory = record
      { _∘_ = _∘⁴_
      ; id = id
      ; assoc = assoc⁴
      ; cancelLeft = cancelLeft⁴
      ; cancelRight  = cancelRight⁴
      }

  F : Two → Two → Four
  F u u = m
  F u v = n
  F v u = o
  F v v = p

  mapᴸ : ∀ {c a b} → a ⇒² b → F a c ⇒⁴ F b c
  mapᴸ id = id
  mapᴸ {u} u⇒v = m⇒o
  mapᴸ {v} u⇒v = n⇒p

  map-∘ᴸ : ∀ {a b c d} (f : a ⇒² b) (g : b ⇒² c) → mapᴸ {d} (g ∘² f) ≡ mapᴸ g ∘⁴ mapᴸ f
  map-∘ᴸ id id = refl
  map-∘ᴸ id u⇒v = sym cancelRight⁴
  map-∘ᴸ u⇒v id = refl

  instance
    functorᴸ : ∀ {b} → Functor categoryI fourCategory (λ a → F a b)
    functorᴸ = record
      { map = mapᴸ
      ; map-id = refl
      ; map-∘ = map-∘ᴸ
      }

  mapᴿ : ∀ {a c d} → c ⇒² d → F a c ⇒⁴ F a d
  mapᴿ id = id
  mapᴿ {u} u⇒v = m⇒n
  mapᴿ {v} u⇒v = o⇒p

  map-∘ᴿ : ∀ {a b c d} (f : a ⇒² b) (g : b ⇒² c) → mapᴿ {d} (g ∘² f) ≡ mapᴿ g ∘⁴ mapᴿ f
  map-∘ᴿ id id = refl
  map-∘ᴿ id u⇒v = sym cancelRight⁴
  map-∘ᴿ u⇒v id = refl

  instance
    functorᴿ : ∀ {a} → Functor categoryI fourCategory (λ b → F a b)
    functorᴿ = record
      { map = mapᴿ
      ; map-id = refl
      ; map-∘ = map-∘ᴿ
      }

  mapDoesn'tCommute : mapᴸ {v} u⇒v ∘⁴ mapᴿ u⇒v ≢ mapᴿ u⇒v ∘⁴ mapᴸ u⇒v
  mapDoesn'tCommute ()

module UniversalProductIsALimit where
  open import Data.Product using (_,_)

  open Structures {{...}}

  data I : Set where aᴵ bᴵ : I

  data _⇒ᴵ_ : I → I → Set where
    idᴵ : ∀ {a} → a ⇒ᴵ a

  _∘ᴵ_ : ∀ {a b c} → (b ⇒ᴵ c) → (a ⇒ᴵ b) → (a ⇒ᴵ c)
  idᴵ ∘ᴵ idᴵ = idᴵ
  
  assocᴵ : ∀ {a b c d} (h : c ⇒ᴵ d) (g : b ⇒ᴵ c) (f : a ⇒ᴵ b) → h ∘ᴵ (g ∘ᴵ f) ≡ (h ∘ᴵ g) ∘ᴵ f
  assocᴵ idᴵ idᴵ idᴵ = refl

  cancelLeftᴵ : ∀ {a b} {f : a ⇒ᴵ b} → idᴵ ∘ᴵ f ≡ f
  cancelLeftᴵ {f = idᴵ} = refl

  cancelRightᴵ : ∀ {a b} {f : a ⇒ᴵ b} → f ∘ᴵ idᴵ ≡ f
  cancelRightᴵ {f = idᴵ} = refl

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
      (cat : Category O _⇒_)
      (one two : O)
      →
      Functor categoryI cat (D one two)
    functorD cat one two = record
      { map = λ
        { {aᴵ} idᴵ → id
        ; {bᴵ} idᴵ → id
        }
      ; map-id = λ
        { {aᴵ} → refl
        ; {bᴵ} → refl
        }
      ; map-∘ = λ
        { {aᴵ} idᴵ idᴵ → sym cancelLeft
        ; {bᴵ} idᴵ idᴵ → sym cancelLeft
        }
      }
      where
        open Category cat

  instance
    fromUniversalProduct : ∀
      {ℓ₁ ℓ₂}
      {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
      {a b c : O}
      {cat : Category O _⇒_}
      (universalProduct : UniversalProduct a b c)
      →
      Limit (functorD cat a b) c
    fromUniversalProduct {c = c} {cat = cat} universalProduct = record
      { cone = record
        { α = λ
          { {aᴵ} → fst
          ; {bᴵ} → snd
          }
        ; naturalTransformation = record
            { naturality = λ
              { {aᴵ} idᴵ → trans cancelRight (sym cancelLeft)
              ; {bᴵ} idᴵ → trans cancelRight (sym cancelLeft)
              }
            }
          }
      ; factor = λ β nt → let m , (p , q) = factor (β aᴵ) (β bᴵ) in m , λ { aᴵ → p ; bᴵ → q }
      }
      where
        open Category cat
        -- "open" doesn't seem to be working the way I expect it to here
        product = UniversalProduct.product universalProduct
        factor = UniversalProduct.factor universalProduct
        fst = Product.fst product
        snd = Product.snd product

open import Data.Product using (_,_; _,′_; proj₁; proj₂)
open import Data.Unit
open import Function using (const)

record TerminalObjectPullbackProduct
    {ℓ₁ ℓ₂}
    {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
    (cat : Category O _⇒_)
    {a b : O}
    (c : O)
    (⊤ : O)
    (f : a ⇒ ⊤)
    (g : b ⇒ ⊤)
    :
    Set (ℓ₁ ⊔ ℓ₂) where
  open Category cat
  open Structures cat
  open Pullback cat f g renaming (Pullback to Pullbackᶠᵍ)

  field
    pullback : Pullbackᶠᵍ c
    terminalObject : TerminalObject ⊤

  open Limit pullback
  open Cone cone
  open NaturalTransformation naturalTransformation
  open TerminalObject terminalObject

  instance
    terminalObjectPullback-UniversalProduct : UniversalProduct a b c
    terminalObjectPullback-UniversalProduct = record
      { product = record
        { fst = α aᴵ
        ; snd = α cᴵ
        }
      ; factor = λ {c′} p q →
          let
            β : ∀ x → const c′ x ⇒ D x
            β = λ
              { aᴵ → p
              ; bᴵ → terminal
              ; cᴵ → q
              }

            nt : NaturalTransformation (Δ catᴵ cat c′) functorD β
            nt = record
              { naturality = λ
                { {aᴵ} idᴵ → trans cancelRight (sym cancelLeft)
                ; {bᴵ} idᴵ → trans cancelRight (sym cancelLeft)
                ; {cᴵ} idᴵ → trans cancelRight (sym cancelLeft)
                ; fᴵ → trans cancelRight (sym uniqueness)
                ; gᴵ → trans cancelRight (sym uniqueness)
                }
              }

            (m , p) = factor β nt
          in
            m , p aᴵ ,′ p cᴵ
      }

record InitialObjectPushoutCoproduct
    {ℓ₁ ℓ₂}
    {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
    (cat : Category O _⇒_)
    {a b : O}
    (c : O)
    (⊥ : O)
    (f : ⊥ ⇒ a)
    (g : ⊥ ⇒ b)
    :
    Set (ℓ₁ ⊔ ℓ₂) where
  open Category cat
  open Structures cat
  open Pushout cat f g renaming (Pushout to Pushoutᶠᵍ)

  field
    pushout : Pushoutᶠᵍ c
    initialObject : InitialObject ⊥

  open Limit pushout
  open Cone cone
  open NaturalTransformation naturalTransformation
  open InitialObject initialObject

  co-pullback : TerminalObjectPullbackProduct op c ⊥ f g
  co-pullback = record
    { pullback = pushout
    ; terminalObject = initialObjectDualOfTerminalObject initialObject
    }
    where
      open Endo.Initial cat
      open Endo.Product cat

  open TerminalObjectPullbackProduct co-pullback

  instance
    initialObjectPushout-UniversalCoproduct : UniversalCoproduct a b c
    initialObjectPushout-UniversalCoproduct =
       subst
         (λ x → Structures.UniversalCoproduct x a b c)
         (cancelDoubleDual cat)
         (universalProductDualOfUniversalCoproduct terminalObjectPullback-UniversalProduct)
      where
        open Endo.Product op
