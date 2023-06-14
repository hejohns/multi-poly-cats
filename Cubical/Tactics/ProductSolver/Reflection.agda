{-# OPTIONS --safe #-}
module Cubical.Tactics.ProductSolver.Reflection where
open import Cubical.Foundations.Prelude
open import Agda.Builtin.Reflection hiding (Type)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
private variable
  ℓ ℓ' : Level
module ReflectionSolver where
  open import Cubical.Tactics.Reflection
  open import Cubical.Data.List
  open import Cubical.Reflection.Base -- `harg` (hidden arg), `varg` (visible arg)
  module _ (bcc : Term {- term denoting the BinaryCartesianCategory -} ) where
    buildExpression : Term → Term -- TODO: check w/ C-c c-d
    buildExpression (def (quote BinaryCartesianCategory.π₁) (ℓ h∷  ℓ' h∷ _ v∷ Γ h∷ Δ h∷ [])) = con ({!!}) []
    buildExpression (def (quote BinaryCartesianCategory.π₂) (ℓ h∷  ℓ' h∷ _ v∷ Γ h∷ Δ h∷ [])) = {!!}
    buildExpression (def (quote BinaryCartesianCategory.⟨_,_⟩) (ℓ h∷ ℓ' h∷ _ v∷ Γ h∷ Δ₁ h∷ Δ₂ h∷ [])) = {!!}
    --buildExpression (def (quote BinaryCartesianCategory.β₁) (ℓ h∷ ℓ' h∷ _ v∷ Γ h∷ Δ₁ h∷ Δ₂ h∷ f h∷ g h∷ [])) = {!!}
    buildExpression (def (quote BinaryCartesianCategory.!) (ℓ h∷ ℓ' h∷ _ v∷ Γ h∷ [])) = {!!}
    buildExpression f = con ({!!}) (f v∷ [])
  solve-macro : Bool -- debug? flag, for equation-solver NOTE: I have no idea what `equation-solver` actually does
              → Term -- term denoting the BinaryCartesianCategory
              → Term -- hole whose goal should be an equality between morphisms in the BinaryCartesianCategory
              → TC Unit -- execute in agda's type checker monad (unify the hole as a side-effect)
  solve-macro debug? bcc = equation-solver (quote BinaryCartesianCategory._×_ ∷ []) mk-call debug? -- TODO
    where
    open import Cubical.Tactics.ProductSolver.Solver
    mk-call : Term -- lhs, as expression (in bcc)
            → Term -- rhs, as expression (in bcc)
            → TC Term -- return path for original goal to agda's type checker monad
    mk-call lhs rhs = returnTC (def (quote Eval.product-solver) (bcc v∷ (buildExpression bcc lhs) v∷ (buildExpression bcc rhs) v∷ (def (quote refl) []) v∷ []))
macro
  solveProd! : Term -- term denoting the BinaryCartesianCategory
             → Term -- hole whose goal should be an equality between morphisms in the BinaryCartesianCategory
             → TC Unit -- execute in agda's type checker monad (unify the hole as a side-effect)
  solveProd! = ReflectionSolver.solve-macro true
