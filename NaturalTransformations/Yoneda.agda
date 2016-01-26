open import Structures.Category

module NaturalTransformations.Yoneda
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  where

open import Data.Product using (∃; _×_; _,_; ,_; proj₁; proj₂)

open import Axioms

open import Structures.Functor
open import Structures.NaturalIsomorphism
open import Structures.NaturalTransformation

open import Categories.SetCat ℓ₂
open import Categories.SetCat (ℓ₁ ⊔ lsuc ℓ₂) renaming (setCategory to setCategory₁)
open import Categories.Functor cat setCategory
open import Categories.Product functorCategory cat

open import Functors.HomFunctor cat

open import Categories.Iso setCategory₁ renaming (_⇔_ to _≈_)

open Category {{...}}
open Functor {{...}}
open NaturalTransformation {{...}}

Yonedaᴸ : Oˣ → Set (ℓ₁ ⊔ lsuc ℓ₂)
Yonedaᴸ ((F , functorF) , a) = ∃ (NaturalTransformation (homFunctor a) functorF)

mapᴸ : ∀ {a b} → (a ⇒ˣ b) → Yonedaᴸ a → Yonedaᴸ b
mapᴸ {(F , functorF) , a} {(G , functorG) , b} ((α , nt-α) , h) (β , nt-β) = γ , nt-γ
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

mapᴸ-id : {a : Oˣ} → mapᴸ (id {a = a}) ≡ id {{setCategory₁}}
mapᴸ-id {(F , functorF) , a} =
  ext λ { (α , nt-α) → cong⟨ (ext λ y → ext λ i → cong (α y) cancelRight) , congNT ⟩ }

mapᴸ-∘ : {a b c : Oˣ} (f : a ⇒ˣ b) (g : b ⇒ˣ c) → mapᴸ (g ∘ f) ≡ mapᴸ g ∘ mapᴸ f
mapᴸ-∘ ((F , functorF) , a) ((G , functorG) , b) =
  ext λ { (β , nt-β) → cong⟨ (ext λ x → ext λ i → cong (G x ∘ F x ∘ β x) (assoc _ _ _)) , congNT ⟩ }

functorᴸ : Functor productCategory setCategory₁ Yonedaᴸ
functorᴸ = record
  { map = mapᴸ
  ; map-id = mapᴸ-id
  ; map-∘ = mapᴸ-∘
  }

Yonedaᴿ : Oˣ → Set (ℓ₁ ⊔ lsuc ℓ₂)
Yonedaᴿ ((F , functorF) , a) = Lift (F a) -- this is inconvenient

mapᴿ : ∀ {a b} → (a ⇒ˣ b) → Yonedaᴿ a → Yonedaᴿ b
mapᴿ {(F , functorF) , a} {(G , functorG) , b} ((α , nt-α) , h) (lift x) = lift (map {{functorG}} h (α a x))

mapᴿ-id : {a : Oˣ} → mapᴿ (id {a = a}) ≡ id {{setCategory₁}}
mapᴿ-id {(F , functorF) , a} = ext λ { (lift x) → cong lift (map-id {{functorF}} $$ x) }

mapᴿ-∘ : {a b c : Oˣ} (f : a ⇒ˣ b) (g : b ⇒ˣ c) → mapᴿ (g ∘ f) ≡ mapᴿ g ∘ mapᴿ f
mapᴿ-∘ {(F , functorF) , a} {(G , functorG) , b} {(H , functorH) , c} ((α , nt-α) , f) ((β , nt-β) , g) =
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

functorᴿ : Functor productCategory setCategory₁ Yonedaᴿ
functorᴿ = record
  { map = mapᴿ
  ; map-id = λ {a} → mapᴿ-id {a}
  ; map-∘ = mapᴿ-∘
  }

NT→functor : ∀ a → Yonedaᴸ a → Yonedaᴿ a
NT→functor ((F , functorF) , a) (α , nt-α) = lift (α a id)

NT→functor′ : ∀
  {a F α}
  {functorF : Functor _ _ F}
  (nt : NaturalTransformation (homFunctor a) functorF α)
  →
  F a
NT→functor′ nt = lower (NT→functor _ (, nt))

functor→NT : ∀ a → Yonedaᴿ a → Yonedaᴸ a
functor→NT ((F , functorF) , a) (lift x) =
  (λ _ → flip map x) , record { naturality = λ f → ext λ g → map-∘ g f $$ x }

functor→NT′ : ∀
  {a F}
  (functorF : Functor _ _ F)
  (x : F a)
  →
  ∃ (NaturalTransformation (homFunctor a) functorF)
functor→NT′ functorF x = functor→NT ((, functorF) , _) (lift x)

naturalityLR : ∀ {a b} (f : a ⇒ˣ b) → NT→functor b ∘ map {{functorᴸ}} f ≡ map {{functorᴿ}} f ∘ NT→functor a
naturalityLR {(F , functorF) , a} {(G , functorG) , b} ((α , nt-α) , h) =
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

naturalityRL : ∀ {a b} (f : a ⇒ˣ b) → functor→NT b ∘ map {{functorᴿ}} f ≡ map {{functorᴸ}} f ∘ functor→NT a
naturalityRL {(F , functorF) , a} {(G , functorG) , b} ((α , nt-α) , h) =
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

private leftId : ∀ x → NT→functor x ∘ functor→NT x ≡ id
leftId ((F , functorF) , a) = ext λ { (lift x) → cong lift (map-id {{functorF}} $$ x) }

private rightId : ∀ x → functor→NT x ∘ NT→functor x ≡ id
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

yonedaLemma : NaturalIsomorphism functorᴸ functorᴿ NT→functor functor→NT
yonedaLemma = record
  { rightNT = record { naturality = naturalityLR }
  ; leftNT = record { naturality = naturalityRL }
  ; leftId = leftId
  ; rightId = rightId
  }

yonedaIso : ∀
  {a F}
  {functorF : Functor _ _ F}
  →
  ∃ (NaturalTransformation (homFunctor a) functorF) ≈ Lift (F a)
yonedaIso {functorF = functorF} = record
  { right = λ nt → lift (NT→functor′ (proj₂ nt))
  ; left = λ p → functor→NT′ functorF (lower p)
  ; rightInverse = leftId ((, functorF) , _)
  ; leftInverse = rightId _
  }
