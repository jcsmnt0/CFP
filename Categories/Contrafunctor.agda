open import Structures.Category

module Categories.Contrafunctor
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {O : Set ℓ₁} {O′ : Set ℓ₃}
  {_⇒_ : O → O → Set ℓ₂} {_⇒′_ : O′ → O′ → Set ℓ₄}
  (cat : Category O _⇒_) (cat′ : Category O′ _⇒′_) 
  where

open import Categories.Functor (Category.op cat) cat′ using (Oᶠ; _⇒ᶠ_) public
open import Categories.Functor (Category.op cat) cat′ using (functorCategory)

open Category functorCategory

instance
  contrafunctorCategory : Category Oᶠ _⇒ᶠ_
  contrafunctorCategory = functorCategory
