{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --safe #-}
module Cubical.Tactics.ProductSolver.Reflection where
open import Cubical.Foundations.Prelude
open import Agda.Builtin.Reflection hiding (Type)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
private variable
  ℓ ℓ' : Level
open import Cubical.Reflection.Base -- `harg` (hidden arg), `varg` (visible arg)
open import Cubical.Data.List
module ReflectionSolver where
  open import Cubical.Tactics.Reflection
  open import Cubical.Categories.Category
  module _ (bcc : Term {- term denoting the BinaryCartesianCategory -} ) where
    buildExpression : Term → Term -- TODO: check w/ C-c c-d
    --buildExpression (def (quote BinaryCartesianCategory.π₁) (ℓ h∷  ℓ' h∷ _ v∷ Γ h∷ Δ h∷ [])) = con ({!!}) []
    --buildExpression (def (quote BinaryCartesianCategory.π₂) (ℓ h∷  ℓ' h∷ _ v∷ Γ h∷ Δ h∷ [])) = {!!}
    --buildExpression (def (quote BinaryCartesianCategory.⟨_,_⟩) (ℓ h∷ ℓ' h∷ _ v∷ Γ h∷ Δ₁ h∷ Δ₂ h∷ [])) = {!!}
    ----buildExpression (def (quote BinaryCartesianCategory.β₁) (ℓ h∷ ℓ' h∷ _ v∷ Γ h∷ Δ₁ h∷ Δ₂ h∷ f h∷ g h∷ [])) = {!!}
    --buildExpression (def (quote BinaryCartesianCategory.!) (ℓ h∷ ℓ' h∷ _ v∷ Γ h∷ [])) = {!!}
    --buildExpression (def (quote Category._⋆_) ([])) = {!!}
    --buildExpression f = con ({!!}) (f v∷ [])
    buildExpression t = t
  open import Cubical.Categories.Category
  solve-macro : Bool -- debug? flag, for equation-solver NOTE: I have no idea what `equation-solver` actually does
              → Term -- term denoting the BinaryCartesianCategory
              → Term -- hole whose goal should be an equality between morphisms in the BinaryCartesianCategory
              → TC Unit -- execute in agda's type checker monad (unify the hole as a side-effect)
              -- `equation-solver` does something like:
              -- - parse the type of the goal
              -- - expects it to be an equation `x ≡ y`
              -- - calls `mk-call x y`
              -- - unifies the result of mk-call w/ the hole
              -- where the first argument is list of terms to *not* normalize, so that our algorithm has something to work with
  solve-macro debug? bcc hole = do
    _ ← debugPrint "tactic" 2 (strErr "foobar" ∷ [])
    equation-solver doNotReduce mk-call debug? hole -- TODO
    where
    -- I'm not sure what's we need here
    doNotReduce = quote Category.id ∷ quote Category._⋆_ ∷ quote BinaryCartesianCategory._×_ ∷ quote BinaryCartesianCategory.π₁ ∷ quote BinaryCartesianCategory.π₂ ∷ quote BinaryCartesianCategory.⟨_,_⟩ ∷ quote BinaryCartesianCategory.⊤ ∷ quote BinaryCartesianCategory.! ∷ []
    open import Cubical.Tactics.ProductSolver.Solver
    mk-call : Term -- lhs of goal, in bcc
            → Term -- rhs of goal, in bcc
            → TC Term -- return path for original goal to agda's type checker monad
    mk-call lhs rhs = do
      _ ← debugPrint "tactic" 2 (strErr "[ProductSolver][mk-call] (" ∷ termErr lhs ∷ strErr ") (" ∷ termErr rhs ∷ strErr ")" ∷ []) 
      _ ← debugPrint "tactic" 2 (strErr "[ProductSolver][mk-call][2] " ∷ termErr (def (quote product-solver-debug) (bcc v∷ (buildExpression bcc lhs) v∷ (buildExpression bcc rhs) v∷ (def (quote refl) []) v∷ [])) ∷ []) 
      returnTC (def (quote product-solver-debug) (bcc v∷ (buildExpression bcc lhs) v∷ (buildExpression bcc rhs) v∷ (def (quote refl) []) v∷ []))
macro
  solveProd! : Term -- term denoting the BinaryCartesianCategory
             → Term -- hole whose goal should be an equality between morphisms in the BinaryCartesianCategory
             → TC Unit -- execute in agda's type checker monad (unify the hole as a side-effect)
  solveProd! bcc hole = do
    _ ← debugPrint "tactic" 2 (strErr "[ProductSolver][solveProd!] (" ∷ termErr bcc ∷ strErr ") " ∷ []) 
    ReflectionSolver.solve-macro true bcc hole
