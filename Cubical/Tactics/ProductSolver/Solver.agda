{-# OPTIONS --safe #-}
module Cubical.Tactics.ProductSolver.Solver where

--      open import Cubical.Categories.Constructions.Free.UnderlyingGraph
--      η : Interp G (cat FreeCartesianCat)
--      η = record { _$g_ = λ x → ↑ x ; _<$g>_ = ↑_ }
--      module Semantics (𝓒 : CartesianCategory ℓₒ ℓₕ)(𝑖 : GraphHom G (Ugr (cat 𝓒))) where
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
private variable
  ℓ ℓ' : Level
module _ (Vertices : Type ℓ) where
  data ProdType : Type ℓ where
    ↑ : Vertices → ProdType
    1ₑ : ProdType
    _×ₑ_ : ProdType → ProdType → ProdType
  module _ (edges[_,_] : ProdType → ProdType → Type ℓ') where
    private variable
      Γ Δ Δ₁ Δ₂ : ProdType
    data Exp[_,_] : ProdType → ProdType → Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      ↑ : edges[ Γ , Δ ] → Exp[ Γ , Δ ]
      !ₑ : Exp[ Γ , 1ₑ ]
      !ₑη : {f : Exp[ Γ , 1ₑ ]} → f ≡ !ₑ
      πₑ₁ : Exp[ (Γ ×ₑ Δ) , Γ ]
      πₑ₂ : Exp[ (Γ ×ₑ Δ) , Δ ]
      _×→ₑ_ : Exp[ Γ , Δ₁ ] → Exp[ Γ , Δ₂ ] → Exp[ Γ , (Δ₁ ×ₑ Δ₂) ]
      _⋆ₑ_ : Exp[ Γ , Δ₁ ] → Exp[ Δ₁ , Δ₂ ] → Exp[ Γ , Δ₂ ]
      βₑ₁ : {f : Exp[ Γ , Δ₁ ]}{g : Exp[ Γ , Δ₂ ]} → (f ×→ₑ g) ⋆ₑ πₑ₁ ≡ f
      βₑ₂ : {f : Exp[ Γ , Δ₁ ]}{g : Exp[ Γ , Δ₂ ]} → (f ×→ₑ g) ⋆ₑ πₑ₂ ≡ g
      ×→ₑη : {f : Exp[ Γ , Δ₁ ×ₑ Δ₂ ]} → ((f ⋆ₑ πₑ₁) ×→ₑ (f ⋆ₑ πₑ₂)) ≡ f
      -- the rest of the Category data
      idₑ : Exp[ Γ , Γ ]
      ⋆ₑIdL : (f : Exp[ Γ , Δ ]) → idₑ ⋆ₑ f ≡ f
      ⋆ₑIdR : (f : Exp[ Γ , Δ ]) → f ⋆ₑ idₑ ≡ f
      ⋆ₑAssoc : (f : Exp[ Γ , Δ₁ ])(g : Exp[ Δ₁ , Δ₂ ])(h : Exp[ Δ₂ , Δ ]) → (f ⋆ₑ g) ⋆ₑ h ≡ f ⋆ₑ (g ⋆ₑ h)
      isSetExp : isSet (Exp[ Γ , Δ ])
    open Category
    open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
    open BinaryCartesianCategory
    Cat : Category _ _
    Cat .ob = ProdType
    Cat .Hom[_,_] = Exp[_,_]
    Cat .id = idₑ
    Cat ._⋆_ = _⋆ₑ_
    Cat .⋆IdL = ⋆ₑIdL
    Cat .⋆IdR = ⋆ₑIdR
    Cat .⋆Assoc = ⋆ₑAssoc
    Cat .isSetHom = isSetExp
    BinCartCat : BinaryCartesianCategory _ _
    BinCartCat .cat = Cat
    BinCartCat ._×_ = _×ₑ_
    BinCartCat .π₁ = πₑ₁
    BinCartCat .π₂ = πₑ₂
    BinCartCat ._×→_ = _×→ₑ_
    BinCartCat .β₁ = βₑ₁
    BinCartCat .β₂ = βₑ₂
    BinCartCat .×→η = ×→ₑη
    BinCartCat .⊤ = 1ₑ
    BinCartCat .! = !ₑ
    BinCartCat .!η = !ₑη
    module Eval where
      open import Cubical.Categories.Constructions.Power
      open import Cubical.Categories.Instances.Sets
      --𝓟 = PowerCategory (Category.ob 𝓒) (SET (ℓ-max ℓ ℓ'))
