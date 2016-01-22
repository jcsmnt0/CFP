open import Structures.Category
open import Structures.Functor

module Proofs.Yoneda
  {ℓ}
  {O : Set ℓ}
  {_⇒_ : O → O → Set ℓ}
  {F : O → Set ℓ}
  (cat : Category O _⇒_)
  where

open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)

open import Axioms

open import Structures.NaturalIsomorphism
open import Structures.NaturalTransformation

open import Categories.SetCat ℓ
open import Categories.SetCat (suc ℓ) renaming (setCategory to setCategory₁)
open import Categories.Functor cat setCategory
open import Categories.Product functorCategory cat

open import Functors.HomFunctor cat

open Category {{...}}
open Functor {{...}}
open NaturalTransformation {{...}}

YonedaLeft : Oˣ → Set (suc ℓ)
YonedaLeft ((F , functorF) , a) = ∃ (NaturalTransformation (homFunctor a) functorF)

mapYL : ∀ {a b} → (a ⇒ˣ b) → YonedaLeft a → YonedaLeft b
mapYL {(F , functorF) , a} {(G , functorG) , b} ((α , nt-α) , h) (β , nt-β) = γ , nt-γ
  where
    γ : ∀ x → HomSet b x → G x
    γ x i = α x (β x (i ∘ h))

    nt-γ : NaturalTransformation (homFunctor b) functorG γ
    nt-γ = record
      { naturality = λ {x} {y} i → ext λ j →
          begin
            α y (β y ((i ∘ j) ∘ h))
          ≡⟨ cong (α y) (cong (β y) (sym (assoc _ _ _))) ⟩
            α y (β y (i ∘ (j ∘ h)))
          ≡⟨ cong (α y) (naturality {{nt-β}} i $$ (j ∘ h)) ⟩
            α y (map {{functorF}} i (β x (j ∘ h)))
          ≡⟨ naturality {{nt-α}} i $$ (β x (j ∘ h)) ⟩
            map {{functorG}} i (α x (β x (j ∘ h)))
          ∎
      }

mapYL-id : {a : Oˣ} → mapYL (id {a = a}) ≡ id
mapYL-id {(F , functorF) , a} =
  ext λ { (α , nt-α) → cong⟨ (ext λ y → ext λ i → cong (α y) cancelRight) , congNT ⟩ }

mapYL-∘ : {a b c : Oˣ} (f : a ⇒ˣ b) (g : b ⇒ˣ c) → mapYL (g ∘ f) ≡ mapYL g ∘ mapYL f
mapYL-∘ ((F , functorF) , a) ((G , functorG) , b) =
  ext λ { (β , nt-β) → cong⟨ (ext λ x → ext λ i → cong (G x ∘ F x ∘ β x) (assoc _ _ _)) , congNT ⟩ }

LeftFunctor : Functor productCategory setCategory₁ YonedaLeft
LeftFunctor = record
  { map = mapYL
  ; map-id = mapYL-id
  ; map-∘ = mapYL-∘
  }

YonedaRight : Oˣ → Set (suc ℓ)
YonedaRight ((F , functorF) , a) = Lift (F a) -- this is inconvenient

mapYR : ∀ {a b} → (a ⇒ˣ b) → YonedaRight a → YonedaRight b
mapYR {(F , functorF) , a} {(G , functorG) , b} ((α , nt-α) , h) (lift x) = lift (map {{functorG}} h (α a x))

mapYR-id : {a : Oˣ} → mapYR (id {a = a}) ≡ id
mapYR-id {(F , functorF) , a} = ext λ { (lift x) → cong lift (map-id {{functorF}} $$ x) }

mapYR-∘ : {a b c : Oˣ} (f : a ⇒ˣ b) (g : b ⇒ˣ c) → mapYR (g ∘ f) ≡ mapYR g ∘ mapYR f
mapYR-∘ {(F , functorF) , a} {(G , functorG) , b} {(H , functorH) , c} ((α , nt-α) , f) ((β , nt-β) , g) =
  ext λ
    { (lift i) → cong lift (
        begin
          map {{functorH}} (g ∘ f) (β a (α a i))
        ≡⟨ map-∘ {{functorH}} f g $$ β a (α a i) ⟩
          map {{functorH}} g (map {{functorH}} f (β a (α a i)))
        ≡⟨ cong (map g) (sym (naturality {{nt-β}} f $$ α a i)) ⟩
          map {{functorH}} g (β b (map {{functorG}} f (α a i)))
        ∎)
    }

RightFunctor : Functor productCategory setCategory₁ YonedaRight
RightFunctor = record
  { map = mapYR
  ; map-id = λ {a} → mapYR-id {a}
  ; map-∘ = mapYR-∘
  }

isoRight : ∀ a → YonedaLeft a → YonedaRight a
isoRight ((F , functorF) , a) (α , nt-α) = lift (α a id)

isoLeft : ∀ a → YonedaRight a → YonedaLeft a
isoLeft ((F , functorF) , a) (lift x) =
  (λ _ → flip map x) , record { naturality = λ f → ext λ g → map-∘ g f $$ x }

naturalityRight : ∀ {a b} (f : a ⇒ˣ b) → isoRight b ∘ map {{LeftFunctor}} f ≡ map {{RightFunctor}} f ∘ isoRight a
naturalityRight {(F , functorF) , a} {(G , functorG) , b} ((α , nt-α) , h) =
  ext λ
    { (β , nt-β) → cong lift (
        begin
          α b (β b (id ∘ h))
        ≡⟨ cong (α b ∘ β b) cancelLeft ⟩
          α b (β b h)
        ≡⟨ cong (α b ∘ β b) (sym cancelRight) ⟩
          α b (β b (h ∘ id))
        ≡⟨ cong (α b) (naturality {{nt-β}} h $$ id) ⟩
          α b (map {{functorF}} h (β a id))
        ≡⟨ naturality {{nt-α}} h $$ β a id ⟩
          map {{functorG}} h (α a (β a id))
        ∎)
    }

naturalityLeft : ∀ {a b} (f : a ⇒ˣ b) → isoLeft b ∘ map {{RightFunctor}} f ≡ map {{LeftFunctor}} f ∘ isoLeft a
naturalityLeft {(F , functorF) , a} {(G , functorG) , b} ((α , nt-α) , h) =
  ext λ
    { (lift x) → cong⟨
        (ext λ c → ext λ i →
          begin
            map {{functorG}} i (map {{functorG}} h (α a x))
          ≡⟨ sym (map-∘ {{functorG}} h i $$ α a x) ⟩
            map {{functorG}} (i ∘ h) (α a x)
          ≡⟨ sym (naturality {{nt-α}} (i ∘ h) $$ x) ⟩
            α c (map {{functorF}} (i ∘ h) x)
          ∎)
      ,
        congNT
      ⟩
    }

leftId : ∀ x → isoRight x ∘ isoLeft x ≡ id
leftId ((F , functorF) , a) = ext λ { (lift x) → cong lift (map-id {{functorF}} $$ x) }

rightId : ∀ x → isoLeft x ∘ isoRight x ≡ id
rightId ((F , functorF) , a) =
  ext λ
    { (α , nt-α) → cong⟨
        (ext λ c → ext λ g →
          begin
            map {{functorF}} g (α a id)
          ≡⟨ sym (naturality {{nt-α}} g $$ id) ⟩
            α c (g ∘ id)
          ≡⟨ cong (α c) cancelRight ⟩
            α c g
          ∎)
      ,
        congNT
      ⟩
    }

YonedaLemma : NaturalIsomorphism LeftFunctor RightFunctor isoRight isoLeft
YonedaLemma = record
  { right = record { naturality = naturalityRight }
  ; left = record { naturality = naturalityLeft }
  ; leftId = leftId
  ; rightId = rightId
  }

