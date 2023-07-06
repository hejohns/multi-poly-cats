{-# OPTIONS --safe #-}
module Cubical.Tactics.ProductSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

private variable
  ℓ ℓ' : Level
module _ (Vertex : Type ℓ) where
  data ProdTypeExpr : Type ℓ where
    ↑̬ : Vertex → ProdTypeExpr
    _×̬_ : ProdTypeExpr → ProdTypeExpr → ProdTypeExpr
    1̬ : ProdTypeExpr
  module _ (Edge[_,_] : ProdTypeExpr → ProdTypeExpr → Type ℓ') where
    open import Cubical.Categories.Constructions.Presented
    open import Cubical.Categories.Constructions.Free.Category -- Quiver
    open Quiver
    --Cone : ProdTypeExpr → ProdTypeExpr → Type _
    --Cone A B = Σ[ C ∈ ProdTypeExpr ] (Σ[ π₁ ∈ ])
    data EdgeExpr[_,_] : ProdTypeExpr → ProdTypeExpr → Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      ↑ₑ : ∀{A B} → Edge[ A , B ] → EdgeExpr[ A , B ]
      --↑ₑ' : Σ[ A ∈ ProdTypeExpr ] (Σ[ B ∈ ProdTypeExpr ] Edge[ A , B ]) → EdgeGenerator
      πₑ₁ : ∀{A B} → EdgeExpr[ A ×̬ B , A ]
      πₑ₂ : ∀{A B} → EdgeExpr[ A ×̬ B , B ]
      _,ₑ_ : {A B C : ProdTypeExpr}(f : EdgeExpr[ C , A ])(g : EdgeExpr[ C , B ]) → EdgeExpr[ C , A ×̬ B ]
      --_,ₑ_ : (A B : ProdTypeExpr)(C : Cone A B) → EdgeGenerator
      !ₑ : ∀{A} → EdgeExpr[ 1̬ , A ]
    data EdgeGenerator : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      coalece : ∀{A B} → EdgeExpr[ A , B ] → EdgeGenerator
    QuiverPresentation : Quiver _ _
    QuiverPresentation .ob = ProdTypeExpr
    QuiverPresentation .mor = EdgeGenerator
    QuiverPresentation .dom (coalece {A} {B} f) = A
    QuiverPresentation .cod (coalece {A} {B} f) = B

    data Equation : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      ×β₁ ×β₂ : ∀{A B C} → EdgeExpr[ C , A ] → EdgeExpr[ C , B ] → Equation
      ×η : ∀{A B C} → EdgeExpr[ C , A ×̬ B ] → Equation
      --×η : ∀{A B C} → (f : EdgeExpr[ C , A ])(g : EdgeExpr[ C , B ])(h : EdgeExpr[ C , A ×̬ B ]) → (h ⋆ π₂)→ Equation
      !η : ∀{A} → EdgeExpr[ 1̬ , A ] → Equation
      
    blah : Category _ _
    blah = PresentedCat QuiverPresentation (mkAx QuiverPresentation Equation flaah)
      where
      flaah : Equation → Σ[ A ∈ QuiverPresentation .ob ] (Σ[ B ∈ QuiverPresentation .ob ] _)
      flaah (×β₁ {A} {B} {C} f g) = C , (A , (↑ (coalece (f ,ₑ g))) ⋆ₑ (↑ (coalece πₑ₁)) , ↑ (coalece f))
      flaah (×β₂ {A} {B} {C} f g) = C , (B , (↑ (coalece (f ,ₑ g))) ⋆ₑ (↑ (coalece πₑ₂)) , ↑ (coalece g))
      flaah (×η {A} {B} {C} f) = {!!} , ({!!} , {!!} , {!!})
      flaah (!η {A} f) = {!!} , ({!!} , {!!} , {!!})
