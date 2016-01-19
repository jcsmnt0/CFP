module Categories.SetCat.EqualityPullback {ℓ} {a b c : Set ℓ} (f : a → b) (g : c → b) where

open import Data.Product using (∃; _,_; proj₁; proj₂)

open import Axioms

open import Structures.Category
open import Structures.Functor
open import Structures.NaturalTransformation

open import Categories.SetCat ℓ

open import Structures.Pullback setCategory f g

open import Functors.Const catᴵ setCategory

open Category {{...}}
open Functor {{...}}
open NaturalTransformation {{...}}

Eq : Set ℓ
Eq = ∃ λ x → f (proj₁ x) ≡ g (proj₂ x)

open Functor (Δ Eq) renaming (map to mapᵟ)

α : ∀ x → const Eq x ⇒ D x
α aᴵ = proj₁ ∘ proj₁
α bᴵ = f ∘ proj₁ ∘ proj₁
α cᴵ = proj₂ ∘ proj₁

naturalityᵟ : ∀ {a b} (h : a ⇒ᴵ b) → α b ∘ mapᵟ h ≡ map h ∘ α a
naturalityᵟ {aᴵ} idᴵ = refl
naturalityᵟ {bᴵ} idᴵ = refl
naturalityᵟ {cᴵ} idᴵ = refl
naturalityᵟ fᴵ = refl
naturalityᵟ gᴵ = ext proj₂

factor : ∀
  {c}
  (β : ∀ x → const c x ⇒ D x)
  (nt : NaturalTransformation (Δ c) functorD β)
  →
  ∃ λ m → (∀ a → β a ≡ α a ∘ m)
factor β nt = (λ x → (((β aᴵ x) , (β cᴵ x)) , trans (sym (naturality fᴵ $$ x)) (naturality gᴵ $$ x))) , λ
  { aᴵ → refl
  ; bᴵ → naturality fᴵ
  ; cᴵ → refl
  }

instance
  EqPullback : Pullback Eq
  EqPullback = record
    { cone = record { naturalTransformation = record { naturality = naturalityᵟ } }
    ; factor = factor
    }
