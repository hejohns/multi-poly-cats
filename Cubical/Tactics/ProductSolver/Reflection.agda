{-# OPTIONS --safe #-}
module Cubical.Tactics.ProductSolver.Reflection where
open import Agda.Builtin.Reflection hiding (Type)
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
open import Cubical.Foundations.Prelude
private variable
  ℓ ℓ' : Level
module ReflectionSolver where
  open import Cubical.Tactics.Reflection
  open import Cubical.Data.List
  open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
  module _ (bcc : BinaryCartesianCategory ℓ ℓ') where
    buildExpression : Term → Term
    buildExpression = ?
  solve-macro : Bool -- debug? flag, for equation-solver NOTE: I have no idea what `equation-solver` actually does
              → BinaryCartesianCategory ℓ ℓ'
              → Term -- hole whose goal should be an equality between morphisms in the BinaryCartesianCategory
              → TC Unit -- execute in agda's type checker monad (unify the hole as a side-effect)
  solve-macro debug? bcc = equation-solver ({!!} ∷ quote BinaryCartesianCategory._×_ ∷ []) mk-call debug?
    where
    mk-call : Term -- lhs?
            → Term -- rhs?
            → TC Term -- ?
    mk-call lhs rhs = returnTC {!def (quote product-solver) (buildExpression)!}
macro
  solveProd! : BinaryCartesianCategory ℓ ℓ'
             → Term -- hole whose goal should be an equality between morphisms in the BinaryCartesianCategory
             → TC Unit -- execute in agda's type checker monad (unify the hole as a side-effect)
  solveProd! = ReflectionSolver.solve-macro true
