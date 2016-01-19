module Proofs.MapDoesn'tAlwaysCommuteBetweenFunctors where

open import Axioms

open import Structures.Functor
open import Structures.Category

open Category {{...}}
open Functor {{...}}

data Two : Set where u v : Two

data _⇒²_ : Two → Two → Set where
  id² : ∀ {x} → x ⇒² x
  u⇒v : u ⇒² v

_∘²_ : ∀ {a b c} → b ⇒² c → a ⇒² b → a ⇒² c
_∘²_ f id² = f
_∘²_ id² f = f

assoc² : ∀ {a b c d} (h : c ⇒² d) (g : b ⇒² c) (f : a ⇒² b) → h ∘² (g ∘² f) ≡ (h ∘² g) ∘² f
assoc² h g id² = refl
assoc² h id² u⇒v = refl

cancelLeft² : ∀ {a b} {f : a ⇒² b} → id² ∘² f ≡ f
cancelLeft² {f = id²} = refl
cancelLeft² {f = u⇒v} = refl

cancelRight² : ∀ {a b} {f : a ⇒² b} → f ∘² id² ≡ f
cancelRight² = refl

instance
  categoryI : Category Two _⇒²_
  categoryI = record
    { _∘_ = _∘²_
    ; id = id²
    ; assoc = assoc²
    ; cancelLeft = cancelLeft²
    ; cancelRight = cancelRight²
    }

data Four : Set where m n o p : Four

data _⇒⁴_ : Four → Four → Set where
  id⁴ : ∀ {x} → x ⇒⁴ x
  m⇒n : m ⇒⁴ n
  m⇒o : m ⇒⁴ o
  m⇒pᴸ : m ⇒⁴ p
  m⇒pᴿ : m ⇒⁴ p
  n⇒p : n ⇒⁴ p
  o⇒p : o ⇒⁴ p

_∘⁴_ : ∀ {a b c} → b ⇒⁴ c → a ⇒⁴ b → a ⇒⁴ c
id⁴ ∘⁴ f = f
g ∘⁴ id⁴ = g
n⇒p ∘⁴ m⇒n = m⇒pᴸ
o⇒p ∘⁴ m⇒o = m⇒pᴿ

assoc⁴ : ∀ {a b c d} (h : c ⇒⁴ d) (g : b ⇒⁴ c) (f : a ⇒⁴ b) → h ∘⁴ (g ∘⁴ f) ≡ (h ∘⁴ g) ∘⁴ f
assoc⁴ id⁴ g f = refl
assoc⁴ m⇒n id⁴ f = refl
assoc⁴ m⇒o id⁴ f = refl
assoc⁴ m⇒pᴸ id⁴ f = refl
assoc⁴ m⇒pᴿ id⁴ f = refl
assoc⁴ n⇒p id⁴ f = refl
assoc⁴ o⇒p id⁴ f = refl
assoc⁴ n⇒p m⇒n id⁴ = refl
assoc⁴ o⇒p m⇒o id⁴ = refl

cancelLeft⁴ : ∀ {a b} {f : a ⇒⁴ b} → id⁴ ∘⁴ f ≡ f
cancelLeft⁴ = refl

cancelRight⁴ : ∀ {a b} {f : a ⇒⁴ b} → f ∘⁴ id⁴ ≡ f
cancelRight⁴ {f = id⁴} = refl
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
    ; id = id⁴
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
mapᴸ id² = id⁴
mapᴸ {u} u⇒v = m⇒o
mapᴸ {v} u⇒v = n⇒p

map-∘ᴸ : ∀ {a b c d} (f : a ⇒² b) (g : b ⇒² c) → mapᴸ {d} (g ∘² f) ≡ mapᴸ g ∘⁴ mapᴸ f
map-∘ᴸ id² id² = refl
map-∘ᴸ id² u⇒v = sym cancelRight⁴
map-∘ᴸ u⇒v id² = refl

functorᴸ : ∀ {b} → Functor categoryI fourCategory (λ a → F a b)
functorᴸ = record
  { map = mapᴸ
  ; map-id = refl
  ; map-∘ = map-∘ᴸ
  }

mapᴿ : ∀ {a c d} → c ⇒² d → F a c ⇒⁴ F a d
mapᴿ id² = id⁴
mapᴿ {u} u⇒v = m⇒n
mapᴿ {v} u⇒v = o⇒p

map-∘ᴿ : ∀ {a b c d} (f : a ⇒² b) (g : b ⇒² c) → mapᴿ {d} (g ∘² f) ≡ mapᴿ g ∘⁴ mapᴿ f
map-∘ᴿ id² id² = refl
map-∘ᴿ id² u⇒v = sym cancelRight⁴
map-∘ᴿ u⇒v id² = refl

functorᴿ : ∀ {a} → Functor categoryI fourCategory (λ b → F a b)
functorᴿ = record
  { map = mapᴿ
  ; map-id = refl
  ; map-∘ = map-∘ᴿ
  }

mapDoesn'tCommute : mapᴸ {v} u⇒v ∘ mapᴿ u⇒v ≢ mapᴿ u⇒v ∘ mapᴸ u⇒v
mapDoesn'tCommute ()
