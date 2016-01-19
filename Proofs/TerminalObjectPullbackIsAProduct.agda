open import Structures.Category

module Proofs.TerminalObjectPullbackIsAProduct
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁} {_⇒_ : O → O → Set ℓ₂}
  {a b : O}
  (cat : Category O _⇒_)
  (c : O)
  (⊤ : O)
  (f : a ⇒ ⊤)
  (g : b ⇒ ⊤)
  where

open import Data.Product using (_,_; _,′_)

open import Axioms

open import Functors.Const

open import Structures.Limit
open import Structures.NaturalTransformation
open import Structures.Pullback cat f g
open import Structures.TerminalObject
open import Structures.UniversalProduct

open Category {{...}}
open Limit {{...}}
open TerminalObject {{...}}

terminalObjectPullback-UniversalProduct : Pullback c → TerminalObject cat ⊤ → UniversalProduct cat a b c
terminalObjectPullback-UniversalProduct pullback terminalObject = record
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
