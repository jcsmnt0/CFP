module Lemmas where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

≤-uniqueness : ∀ {a b} {p q : a ≤ b} → p ≡ q
≤-uniqueness {p = z≤n} {q = z≤n} = refl
≤-uniqueness {p = s≤s _} {q = s≤s _} = cong s≤s ≤-uniqueness
