{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.Util where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality hiding (id; sym)
  renaming ( _≡_ to Eq
           ; refl to reflEq
           )


private variable
  ℓ : Level
  A B C : Type ℓ
  w x y z : A

ap₂ : (f : A → B → C) → Eq w x → Eq y z → Eq (f w y) (f x z)
ap₂ _ reflEq reflEq = reflEq
