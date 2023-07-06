{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
private variable ℓ ℓ' : Level
module _ (Vertex : Type ℓ) where
  data ProdTypeExpr : Type ℓ where
    ↑̬ : Vertex → ProdTypeExpr
    _×̬_ : ProdTypeExpr → ProdTypeExpr → ProdTypeExpr
    ⊤̬ : ProdTypeExpr
  module _ (Edge : Type ℓ')(dom : Edge → ProdTypeExpr)(cod : Edge → ProdTypeExpr) where
    open BinaryCartesianCategory
    open Category
    data EdgeExpr[_,_] : ProdTypeExpr → ProdTypeExpr → Type (ℓ-max ℓ ℓ') where
      ↑ₑ : (e : Edge) → EdgeExpr[ dom e , cod e ]
      idₑ : ∀{A} → EdgeExpr[ A , A ]
      _⋆ₑ_ : ∀{A B C} → EdgeExpr[ A , B ] → EdgeExpr[ B , C ] → EdgeExpr[ A , C ]
      ⋆ₑIdL : ∀{A B}(f : EdgeExpr[ A , B ]) → idₑ ⋆ₑ f ≡ f
      ⋆ₑIdR : ∀{A B}(f : EdgeExpr[ A , B ]) → f ⋆ₑ idₑ ≡ f
      ⋆ₑAssoc : ∀{A B C D}(f : EdgeExpr[ A , B ])(g : EdgeExpr[ B , C ])(h : EdgeExpr[ C , D ]) → (f ⋆ₑ g) ⋆ₑ h ≡ f ⋆ₑ (g ⋆ₑ h)
      isSetEdgeExpr : ∀{A B} → isSet EdgeExpr[ A , B ]
      π₁ₑ : ∀{A B} → EdgeExpr[ A ×̬ B , A ]
      π₂ₑ : ∀{A B} → EdgeExpr[ A ×̬ B , B ]
      ⟨_,ₑ_⟩ : ∀{A B C} → EdgeExpr[ C , A ] → EdgeExpr[ C , B ] → EdgeExpr[ C , A ×̬ B ]
      !ₑ : ∀{A} → EdgeExpr[ A , ⊤̬ ]
      ×̬β₁ : ∀{A B C}{f : EdgeExpr[ C , A ]}{g : EdgeExpr[ C , B ]} → ⟨ f ,ₑ g ⟩ ⋆ₑ π₁ₑ ≡ f
      ×̬β₂ : ∀{A B C}{f : EdgeExpr[ C , A ]}{g : EdgeExpr[ C , B ]} → ⟨ f ,ₑ g ⟩ ⋆ₑ π₂ₑ ≡ g
      ×̬η : ∀{A B C}{f : EdgeExpr[ C , A ×̬ B ]} → ⟨ f ⋆ₑ π₁ₑ ,ₑ f ⋆ₑ π₂ₑ ⟩ ≡ f
      ⊤ₑη : ∀{A}{f : EdgeExpr[ A , ⊤̬ ]} → f ≡ !ₑ
    FreeCartesianCategory : BinaryCartesianCategory _ _
    FreeCartesianCategory .cat .ob = ProdTypeExpr
    FreeCartesianCategory .cat .Hom[_,_] = EdgeExpr[_,_]
    FreeCartesianCategory .cat .id = idₑ
    FreeCartesianCategory .cat ._⋆_ = _⋆ₑ_
    FreeCartesianCategory .cat .⋆IdL = ⋆ₑIdL
    FreeCartesianCategory .cat .⋆IdR = ⋆ₑIdR
    FreeCartesianCategory .cat .⋆Assoc = ⋆ₑAssoc
    FreeCartesianCategory .cat .isSetHom = isSetEdgeExpr
    FreeCartesianCategory ._×_ = _×̬_
    FreeCartesianCategory .⊤ = ⊤̬
    FreeCartesianCategory .π₁ = π₁ₑ
    FreeCartesianCategory .π₂ = π₂ₑ
    FreeCartesianCategory .⟨_,_⟩ = ⟨_,ₑ_⟩
    FreeCartesianCategory .! = !ₑ
    FreeCartesianCategory .×β₁ = ×̬β₁
    FreeCartesianCategory .×β₂ = ×̬β₂
    FreeCartesianCategory .×η = ×̬η
    FreeCartesianCategory .⊤η = ⊤ₑη
