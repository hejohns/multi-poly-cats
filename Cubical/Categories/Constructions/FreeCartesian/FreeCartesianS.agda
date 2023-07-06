{-# OPTIONS --safe #-}

-- TODO: rename after I stub this out
module Cubical.Categories.Constructions.FreeCartesian.FreeCartesianS where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Graph.Base
open import Cubical.Data.FinSet
private variable ℓ̬ ℓₑ : Level
module _ (G : Graph ℓ̬ ℓₑ) where
    data FreeCartesianObjects : Type (ℓ-suc ℓ̬) where
        ↑_ : (A : Node G) → FreeCartesianObjects
        Π : (J : FinSet ℓ-zero) → FreeCartesianObjects
