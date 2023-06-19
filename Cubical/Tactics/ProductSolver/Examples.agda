{-# OPTIONS -v tactic:100 #-}
module Cubical.Tactics.ProductSolver.Examples where

open import Cubical.Foundations.Prelude
private variable
  ℓ ℓ' : Level
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
module Examples (bcc : BinaryCartesianCategory ℓ ℓ') where
  open import Cubical.Categories.Category
  open BinaryCartesianCategory
  open Category
  private variable
    Γ Δ : bcc .cat .ob
  open import Cubical.Tactics.CategorySolver.Reflection
  _ : {f : bcc .cat [ Γ , Δ ]} → (f ⋆⟨ bcc .cat ⟩ bcc .cat .id) ≡ f
  _ = solveCat! (bcc .cat)
  _ : (f : bcc .cat [ Γ , Δ ]) → (f ⋆⟨ bcc .cat ⟩ bcc .cat .id) ≡ f
  _ = λ f → solveCat! (bcc .cat)
  open import Cubical.Tactics.ProductSolver.Reflection
  _ : {f : bcc .cat [ Γ , Δ ]} → (f ⋆⟨ bcc .cat ⟩ bcc .cat .id) ≡ f
  _ = {!solveProd! bcc!}
