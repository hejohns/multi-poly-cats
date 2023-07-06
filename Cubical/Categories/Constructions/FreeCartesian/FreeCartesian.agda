{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where
open import Cubical.Foundations.Prelude
private variable ℓ ℓ' : Level
private variable ℓq ℓq' : Level
private variable ℓc ℓc' : Level
open import Cubical.Categories.Category
open Category
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
open BinaryCartesianCategory
-- generating data
module Data where
  module _ (Vertex : Type ℓ) where
    data ProdTypeExpr : Type ℓ where
      ↑̬ : Vertex → ProdTypeExpr
      _×̬_ : ProdTypeExpr → ProdTypeExpr → ProdTypeExpr
      ⊤̬ : ProdTypeExpr
  -- TODO: what is going on with these level variables
  record PseudoQuiver ℓq ℓq' : Type (ℓ-suc (ℓ-max ℓq ℓq')) where
    field
      vertex : Type ℓq
      edge : Type ℓq'
      dom : edge → ProdTypeExpr vertex
      cod : edge → ProdTypeExpr vertex
  open PseudoQuiver
  interpret-objects : (Q : PseudoQuiver ℓq ℓq')(𝓒 : BinaryCartesianCategory ℓc ℓc') → (Q .vertex → 𝓒 .cat .ob) → ProdTypeExpr (Q .vertex) → 𝓒 .cat .ob
  interpret-objects Q 𝓒 ı (↑̬ A) = ı A
  interpret-objects Q 𝓒 ı (A ×̬ B) = interpret-objects Q 𝓒 ı A ×⟨ 𝓒 ⟩ interpret-objects Q 𝓒 ı B
  interpret-objects Q 𝓒 ı ⊤̬ = 𝓒 .⊤
  record Interp (Q : PseudoQuiver ℓq ℓq')(𝓒 : BinaryCartesianCategory ℓc ℓc') : Type (ℓ-max (ℓ-max ℓq ℓq') (ℓ-max ℓc ℓc')) where
    field
      I-ob : Q .vertex → 𝓒 .cat .ob 
      I-hom : (e : Q .edge) → 𝓒 .cat [ interpret-objects Q 𝓒 I-ob (Q .dom e) , interpret-objects Q 𝓒 I-ob (Q .cod e) ]
open Data
open PseudoQuiver
module _ (Q : PseudoQuiver ℓq ℓq') where
  ProdTypeExpr' = ProdTypeExpr (Q .vertex)
  data EdgeExpr[_,_] : ProdTypeExpr' → ProdTypeExpr' → Type (ℓ-max ℓq ℓq') where
    ↑ₑ : (e : Q .edge) → EdgeExpr[ Q .dom e , Q .cod e ]
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
    ⊤̬η : ∀{A}{f : EdgeExpr[ A , ⊤̬ ]} → f ≡ !ₑ
  FreeCartesianCategory : BinaryCartesianCategory _ _
  FreeCartesianCategory .cat .ob = ProdTypeExpr'
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
  FreeCartesianCategory .⊤η = ⊤̬η
  open Interp
  lemma : (A : ProdTypeExpr') → interpret-objects Q FreeCartesianCategory ↑̬ A ≡ A
  lemma (↑̬ B) = refl
  lemma (B ×̬ C) = λ i → lemma B i ×̬ lemma C i
  lemma ⊤̬  = refl
  η : Interp Q FreeCartesianCategory
  η .I-ob = ↑̬
  η .I-hom e = transport (congS (λ x → EdgeExpr[ x , Q .cod e ]) (sym (lemma (Q .dom e))) ∙ congS (λ x → EdgeExpr[ interpret-objects Q FreeCartesianCategory ↑̬  (Q .dom e) , x ]) (sym (lemma (Q .cod e)))) (↑ₑ e)
  -- EdgeExpr[ (Q .dom e) , (Q .cod e) ]
  -- ≡
  -- EdgeExpr[
  --       (Q .dom e) ,
  --       interpret-objects Q FreeCartesianCategory ↑̬ (Q .cod e) ]
  -- ≡
  -- EdgeExpr[
  --       interpret-objects Q FreeCartesianCategory ↑̬ (Q .dom e) ,
  --       interpret-objects Q FreeCartesianCategory ↑̬ (Q .cod e) ]
