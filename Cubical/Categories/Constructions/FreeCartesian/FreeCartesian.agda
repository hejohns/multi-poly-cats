{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Graph.Base

private variable ℓv ℓe : Level

module _ (G : Graph ℓv ℓe) where
