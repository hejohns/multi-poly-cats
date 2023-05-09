{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base

private variable ℓₒ ℓₕ : Level

module _ (𝓒 : Category ℓₒ ℓₕ) where
    open Cubical.Categories.Category.Base.Category
    data Foobar : Type ℓₒ where
        iddd : (A : ob 𝓒) → Foobar
        pair : (A B : Foobar) → Foobar
        idd : (A B : Foobar) → pair A B ≡ pair B A
        assoc : (A B C : Foobar) → pair A (pair B C) ≡ pair (pair A B) C
    FreeCartesianCat : Category ℓₒ ℓₕ
    FreeCartesianCat = record
                        { ob = Foobar
                        ; Hom[_,_] = {!!}
                        ; id = {!!}
                        ; _⋆_ = {!!}
                        ; ⋆IdL = {!!}
                        ; ⋆IdR = {!!}
                        ; ⋆Assoc = {!!}
                        ; isSetHom = {!!}
                        }
