open import Structures.Category

module NaturalTransformations.CoYoneda
  {ℓ₁ ℓ₂}
  {O : Set ℓ₁}
  {_⇒_ : O → O → Set ℓ₂}
  (cat : Category O _⇒_)
  where

open import Structures.NaturalIsomorphism

open import NaturalTransformations.Yoneda (Category.op cat) public using ()
  renaming (
    NT→functor to NT→contrafunctor;
    functor→NT to contrafunctor→NT;
    NT→functor′ to NT→contrafunctor′;
    functor→NT′ to contrafunctor→NT′;
    yonedaLemma to coYonedaLemma;
    yonedaIso to coYonedaIso)
