module Structures.Monoid ℓ where

open import Data.Product using (Σ-syntax; _,_)

open import Axioms

open import Categories.SetCat ℓ

open import Structures.Category
open import Structures.Functor

open Category {{...}}

record Monoid : Set (suc ℓ) where
  field
    Carrier : Set ℓ
    ε : Carrier
    _⋆_ : Carrier → Carrier → Carrier
    ⋆-assoc : ∀ x y z → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z
    ε-cancelLeft : ∀ {x} → ε ⋆ x ≡ x
    ε-cancelRight : ∀ {x} → x ⋆ ε ≡ x

  open import Data.List using (List; foldl)

  crush : Carrier → List Carrier → Carrier
  crush = foldl _⋆_

open Monoid {{...}}

record Homomorphism (m n : Monoid) : Set ℓ where
  constructor homomorphism

  field
    mmap : Carrier {{m}} → Carrier {{n}}
    distributivity : ∀ x y → mmap (x ⋆ y) ≡ mmap x ⋆ mmap y
    ε-preservation : mmap ε ≡ ε

_⇒ᴹ_ : Monoid → Monoid → Set ℓ
_⇒ᴹ_ = Homomorphism

open Homomorphism {{...}}

_∘ᴹ_ : ∀ {m n l} → (n ⇒ᴹ l) → (m ⇒ᴹ n) → (m ⇒ᴹ l)
g ∘ᴹ f = record
  { mmap = mmap ∘ mmap
  ; distributivity = λ _ _ → trans (cong mmap (distributivity _ _)) (distributivity _ _)
  ; ε-preservation = trans (cong mmap ε-preservation) ε-preservation
  }

cong-homomorphism : ∀
  {m n}
  {f g : m ⇒ᴹ n}
  (p : mmap {{f}} ≡ mmap {{g}})
  →
  f ≡ g
cong-homomorphism refl =
  cong₂ (homomorphism _) (ext λ _ → ext λ _ → K) K

idᴹ : ∀ {m} → m ⇒ᴹ m
idᴹ = record { mmap = id ; distributivity = λ _ _ → refl ; ε-preservation = refl }

instance
  monoidCategory : Category Monoid Homomorphism
  monoidCategory = record
    { _∘_ = _∘ᴹ_
    ; id = idᴹ
    ; assoc = λ _ _ _ → cong-homomorphism refl
    ; cancelLeft = cong-homomorphism refl
    ; cancelRight = cong-homomorphism refl
    }

instance
  monoidFunctor : Functor monoidCategory setCategory Monoid.Carrier
  monoidFunctor = record
    { map = Homomorphism.mmap
    ; map-id = refl
    ; map-∘ = λ _ _ → refl
    }

open Functor monoidFunctor

record FreeMonoid (x : Set ℓ) (m : Monoid) (p : x ⇒ Monoid.Carrier m) : Set (suc ℓ) where
  field
    factor :
      (n : Monoid)
      (q : x ⇒ Carrier {{n}})
      →
      Σ[ h ∈ m ⇒ᴹ n ] q ≡ map h ∘ p 

