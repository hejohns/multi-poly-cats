{-# OPTIONS --safe #-}
module Cubical.Tactics.ProductSolver.Solver where
open import Cubical.Foundations.Prelude
private variable ℓ ℓ' : Level
open import Cubical.Categories.Category
open Category
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
open BinaryCartesianCategory
module Eval (𝓒 : BinaryCartesianCategory ℓ ℓ') where
  open import Cubical.Categories.Constructions.FreeCartesian.FreeCartesian
  data Edge : Type (ℓ-max ℓ ℓ') where
    coalece : ∀{A B} → (𝓒 .cat) [ A , B ] → Edge
  cod : Edge → ProdTypeExpr (𝓒 .cat .ob)
  cod (coalece {A} {B} f) = ↑̬ A
  dom : Edge → ProdTypeExpr (𝓒 .cat .ob)
  dom (coalece {A} {B} f) = ↑̬ B
  Expr : BinaryCartesianCategory _ _
  Expr = FreeCartesianCategory (𝓒 .cat .ob) Edge cod dom
  open StrictCartesianFunctor
  open import Cubical.Categories.Functor
  open Functor
  reinterpret-objects : Expr .cat .ob → 𝓒 .cat .ob
  reinterpret-objects (↑̬ A) = A
  reinterpret-objects (A ×̬ B) = reinterpret-objects A ×⟨ 𝓒 ⟩ reinterpret-objects B
  reinterpret-objects ⊤̬ = 𝓒 .⊤
  reinterpret-morphisms : ∀{A B} → Expr .cat [ A , B ] → (𝓒 .cat) [ reinterpret-objects A , reinterpret-objects B ]
  reinterpret-morphisms (↑ₑ (coalece e))= e
  reinterpret-morphisms idₑ = 𝓒 .cat .id
  reinterpret-morphisms (f ⋆ₑ g) = reinterpret-morphisms f ⋆⟨ 𝓒 .cat ⟩ reinterpret-morphisms g
  reinterpret-morphisms (⋆ₑIdL f i) = 𝓒 .cat .⋆IdL (reinterpret-morphisms f) i
  reinterpret-morphisms (⋆ₑIdR f i) = 𝓒 .cat .⋆IdR (reinterpret-morphisms f) i
  reinterpret-morphisms (⋆ₑAssoc f g h i) = 𝓒 .cat .⋆Assoc (reinterpret-morphisms f) (reinterpret-morphisms g) (reinterpret-morphisms h) i
  reinterpret-morphisms (isSetEdgeExpr i j k l m n) = 𝓒 .cat .isSetHom (reinterpret-morphisms i) (reinterpret-morphisms j) (congS reinterpret-morphisms k) (congS reinterpret-morphisms l) m n -- NOTE: I typed random stuff and crossed my fingers. I don't want to think about what this is supposed to be
  reinterpret-morphisms π₁ₑ = 𝓒 .π₁
  reinterpret-morphisms π₂ₑ = 𝓒 .π₂
  reinterpret-morphisms ⟨ f ,ₑ g ⟩ = 𝓒 .⟨_,_⟩ (reinterpret-morphisms f) (reinterpret-morphisms g)
  reinterpret-morphisms !ₑ = 𝓒 .!
  reinterpret-morphisms (×̬β₁ {A} {B} {C} {f} {g} i) = 𝓒 .×β₁ {reinterpret-objects A} {reinterpret-objects B} {reinterpret-objects C} {reinterpret-morphisms f} {reinterpret-morphisms g} i
  reinterpret-morphisms (×̬β₂ {A} {B} {C} {f} {g} i) = 𝓒 .×β₂ {reinterpret-objects A} {reinterpret-objects B} {reinterpret-objects C} {reinterpret-morphisms f} {reinterpret-morphisms g} i
  reinterpret-morphisms (×̬η {A} {B} {C} {f} i) = 𝓒 .×η {reinterpret-objects A} {reinterpret-objects B} {reinterpret-objects C} {reinterpret-morphisms f} i
  reinterpret-morphisms (⊤̬η {A} {f} i) = 𝓒 .⊤η {reinterpret-objects A} {reinterpret-morphisms f} i
  reinterpret : StrictCartesianFunctor Expr 𝓒
  reinterpret .functor .F-ob = reinterpret-objects
  reinterpret .functor .F-hom = reinterpret-morphisms
  reinterpret .functor .F-id = refl
  reinterpret .functor .F-seq _ _ = refl
  reinterpret .respects-⊤ = refl
  reinterpret .respects-× = refl
