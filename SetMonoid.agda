module SetMonoid where

open import Data.Product using (Σ-syntax; _,_)
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Axioms
open import Categories
open import SetCat

module ListFreeMonoid {ℓ} (X : Set ℓ) where
  open import Data.List using (List; [_]; []; _∷_; _++_; foldl)

  open Category (setCategory ℓ)
  open Structures (setCategory ℓ)
  open import Monoids ℓ

  open ListEndofunctor ℓ
  open Functor {{...}}
  open Monoid {{...}}

  []-cancelRight : {a : Set ℓ} {xs : List a} → xs ++ [] ≡ xs
  []-cancelRight {xs = []} = refl
  []-cancelRight {xs = _ ∷ _} = cong (_∷_ _) []-cancelRight

  ++-assoc : {a : Set ℓ} (xs ys zs : List a) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

  instance
    ListMonoid : Monoid
    ListMonoid = record
      { Carrier = List X
      ; ε = []
      ; _⋆_ = _++_
      ; ε-cancelLeft = refl
      ; ε-cancelRight = []-cancelRight
      ; ⋆-assoc = ++-assoc
      }

  foldl-distributivity :
    (m : Monoid)
    (x : Monoid.Carrier m)
    (xs ys : List (Monoid.Carrier m))
    →
    crush x (xs ++ ys) ≡ crush x xs ⋆ crush ε ys
  foldl-distributivity m x [] [] = sym ε-cancelRight
  foldl-distributivity m x [] (y ∷ ys) =
    begin
      crush (x ⋆ y) ys
    ≡⟨ foldl-distributivity m (x ⋆ y) [] ys ⟩
      (x ⋆ y) ⋆ crush ε ys
    ≡⟨ sym (⋆-assoc _ _ _) ⟩
      x ⋆ (y ⋆ crush ε ys)
    ≡⟨ cong (_⋆_ x) (sym (foldl-distributivity m y [] ys)) ⟩
      x ⋆ crush y ys
    ≡⟨ cong (λ y′ → x ⋆ crush y′ ys) (sym ε-cancelLeft) ⟩
      x ⋆ crush (ε ⋆ y) ys
    ∎
  foldl-distributivity m x (y ∷ xs) ys = foldl-distributivity m (x ⋆ y) xs ys

  map-distributivity :
    {a b : Set ℓ}
    (f : a → b)
    (xs ys : List a)
    →
    map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-distributivity f [] ys = refl
  map-distributivity f (x ∷ xs) ys = cong (_∷_ (f x)) (map-distributivity f xs ys)

  crushMap-distributivity :
    (m : Monoid)
    (q : X ⇒ Monoid.Carrier m)
    (xs ys : List X)
    →
    crush ε (map q (xs ++ ys)) ≡ crush ε (map q xs) ⋆ crush ε (map q ys)
  crushMap-distributivity m q [] _ = sym ε-cancelLeft
  crushMap-distributivity m q (x ∷ xs) ys = 
    begin
      crush (ε ⋆ q x) (map q (xs ++ ys))
    ≡⟨ cong (crush (ε ⋆ q x)) (map-distributivity q xs ys) ⟩
      crush (ε ⋆ q x) (map q xs ++ map q ys)
    ≡⟨ foldl-distributivity m (ε ⋆ q x) (map q xs) (map q ys) ⟩
      (crush (ε ⋆ q x) (map q xs)) ⋆ (crush ε (map q ys))
    ∎

  crushMapHomomorphism : ∀ n → (X ⇒ Monoid.Carrier n) → (ListMonoid ⇒ᴹ n)
  crushMapHomomorphism n q = record
    { mmap = crush ε ∘ map q
    ; distributivity = crushMap-distributivity n q
    ; ε-preservation = refl
    }

  factor :
    (n : Monoid)
    (q : X ⇒ Monoid.Carrier n)
    →
    Σ[ h ∈ ListMonoid ⇒ᴹ n ] (q ≡ map h ∘ [_])
  factor n q = crushMapHomomorphism n q , ext (λ _ → sym ε-cancelLeft)

  instance
    ListFreeMonoid : FreeMonoid X ListMonoid [_]
    ListFreeMonoid = record { factor = factor }

