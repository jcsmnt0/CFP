module Categories.SetCat.EqualityEqualizer {ℓ} {a b : Set ℓ} (f g : a → b) where

open import Data.Product using (∃; Σ-syntax; _,_; proj₁; proj₂)

open import Axioms

open import Structures.Category
open import Structures.Functor
open import Structures.NaturalTransformation

open import Categories.SetCat ℓ

open import Structures.Equalizer setCategory f g

open import Functors.Const catᴵ setCategory

open Category {{...}}
open Functor {{...}}
open NaturalTransformation {{...}}

Eq : Set ℓ
Eq = ∃ λ x → f x ≡ g x

open Functor (Δ Eq) renaming (map to mapᵟ)

α : ∀ x → const Eq x ⇒ D x
α {aᴵ} = proj₁
α {bᴵ} = f ∘ proj₁

naturalityᵟ : ∀ {a b} (f : a ⇒ᴵ b) → α b ∘ mapᵟ f ≡ map f ∘ α a
naturalityᵟ {aᴵ} idᴵ = refl
naturalityᵟ {bᴵ} idᴵ = refl
naturalityᵟ fᴵ = refl
naturalityᵟ gᴵ = ext proj₂

factor : ∀
  {c}
  (β : ∀ x → const c x ⇒ D x)
  (nt : NaturalTransformation (Δ c) functorD β)
  →
  Σ[ m ∈ (c ⇒ Eq) ] (∀ a → β a ≡ α a ∘ m)
factor β nt = (λ x → β aᴵ x , trans (sym (naturality fᴵ $$ x)) (naturality gᴵ $$ x)) , λ
  { aᴵ → refl
  ; bᴵ → naturality fᴵ
  }

instance
  EqEqualizer : Equalizer Eq
  EqEqualizer = record
    { cone = record { naturalTransformation = record { naturality = naturalityᵟ } }
    ; factor = factor
    }
