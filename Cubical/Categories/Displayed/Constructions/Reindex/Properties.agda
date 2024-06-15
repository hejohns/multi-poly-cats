{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Constructions.Reindex.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open UniversalElement
open UniversalElementᴰ
open CartesianOver

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D
    F*Dᴰ = reindex Dᴰ F
    module R = HomᴰReasoning Dᴰ
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  module _
    {c : C .ob}{c' : C .ob}
    {dᴰ' : Dᴰ.ob[ F ⟅ c' ⟆ ]}{f : C [ c , c' ]}
    where
    reflectsCartesianOvers
      : CartesianOver Dᴰ dᴰ' (F ⟪ f ⟫)
      → CartesianOver F*Dᴰ dᴰ' f
    reflectsCartesianOvers f-lift .f*cᴰ' = f-lift .f*cᴰ'
    reflectsCartesianOvers f-lift .π = f-lift .π
    reflectsCartesianOvers f-lift .isCartesian {c''} dᴰ'' g gfᴰ = uniqueExists
      (⟨gfᴰ⟩' .fst .fst)
      ⟨gfᴰ⟩'-commutes
      (λ _ → F*Dᴰ.isSetHomᴰ _ _)
      ⟨gfᴰ⟩'-uniq
      where
        gfᴰ' : Dᴰ.Hom[ _ ][ dᴰ'' , dᴰ' ]
        gfᴰ' = R.reind (F .F-seq g f) gfᴰ

        ⟨gfᴰ⟩' = f-lift .isCartesian dᴰ'' (F ⟪ g ⟫) gfᴰ'

        ⟨gfᴰ⟩'-commutes : ⟨gfᴰ⟩' .fst .fst F*Dᴰ.⋆ᴰ f-lift .π ≡ gfᴰ
        ⟨gfᴰ⟩'-commutes = R.≡[]-rectify (R.≡[]∙ _ _ (R.≡[]∙ _ _
          (R.reind-filler-sym (F .F-seq g f) _)
          (⟨gfᴰ⟩' .fst .snd))
          (symP (R.reind-filler (F .F-seq g f) gfᴰ)))

        ⟨gfᴰ⟩'-uniq
          : (gᴰ : F*Dᴰ.Hom[ g ][ dᴰ'' , f-lift .f*cᴰ' ])
          → (gᴰ F*Dᴰ.⋆ᴰ f-lift .π) ≡ gfᴰ
          → ⟨gfᴰ⟩' .fst .fst ≡ gᴰ
        ⟨gfᴰ⟩'-uniq gᴰ gᴰ-commutes = cong fst (⟨gfᴰ⟩' .snd (gᴰ ,
          (R.≡[]-rectify (R.≡[]∙ _ _ (R.≡[]∙ _ _
            (R.reind-filler (sym (F .F-seq _ _)) _)
            gᴰ-commutes)
            (R.reind-filler (F .F-seq g f) gfᴰ)))))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where

  reindReflectsVerticalTerminal :
    ∀ c → VerticalTerminalAt Dᴰ (F ⟅ c ⟆)
    → VerticalTerminalAt (reindex Dᴰ F) c
  reindReflectsVerticalTerminal c 𝟙ᴰ .vertexᴰ = 𝟙ᴰ .vertexᴰ
  reindReflectsVerticalTerminal c 𝟙ᴰ .elementᴰ = 𝟙ᴰ .elementᴰ
  reindReflectsVerticalTerminal c 𝟙ᴰ .universalᴰ = 𝟙ᴰ .universalᴰ

  VerticalTerminalsReindex :
    VerticalTerminals Dᴰ
    → VerticalTerminals (reindex Dᴰ F)
  VerticalTerminalsReindex vta c =
    reindReflectsVerticalTerminal c (vta (F ⟅ c ⟆))

  module _ {termC : Terminal' C} where
    open Terminal'Notation termC
    LiftedTerminalReindex :
      VerticalTerminalAt Dᴰ (F ⟅ 𝟙 ⟆)
      → LiftedTerminal (reindex Dᴰ F) termC
    LiftedTerminalReindex 𝟙ᴰ =
      Vertical/𝟙→LiftedTerm _
        (reindReflectsVerticalTerminal (termC .vertex) 𝟙ᴰ)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} where
  open import Cubical.Categories.Displayed.BinProduct
  open import Cubical.Categories.Displayed.Instances.Sets.Base
  open import Cubical.Categories.Displayed.Functor
  open import Cubical.Categories.Displayed.Constructions.BinProduct.More
  open import Cubical.Categories.Adjoint.UniversalElements
  open import Cubical.Categories.Instances.Sets
  open Functorᴰ
  open HomᴰReasoning Dᴰ -- do all the equation reasoning in the "reference space" Dᴰ
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Rᴰ = Categoryᴰ (reindex Dᴰ F)
  module _ {c : C .ob} (Fcᴰ Fcᴰ' : Dᴰ.ob[ F ⟅ c ⟆ ])
    (vbp : VerticalBinProductsAt Dᴰ (Fcᴰ , Fcᴰ')) where
    private
      module V = VerticalBinProductsAtNotation vbp
      reind-π₁₂ : Dᴰ.Hom[ F ⟪ C .id ⟫ ][ V.vert-cᴰ×cᴰ' , Fcᴰ ] ×
        Dᴰ.Hom[ F ⟪ C .id ⟫ ][ V.vert-cᴰ×cᴰ' , Fcᴰ' ]
      reind-π₁₂ .fst = reind (sym (F .F-id)) V.vert-π₁
      reind-π₁₂ .snd = reind (sym (F .F-id)) V.vert-π₂

    reindReflectsVerticalBinProd : VerticalBinProductsAt (reindex Dᴰ F) (Fcᴰ , Fcᴰ')
    reindReflectsVerticalBinProd .vertexᴰ = V.vert-cᴰ×cᴰ'
    reindReflectsVerticalBinProd .elementᴰ = reind-π₁₂
    reindReflectsVerticalBinProd .universalᴰ {x = x} {xᴰ = xᴰ} {f = f} .equiv-proof =
      λ cone → goal cone
      where
      goal : (cone : Dᴰ.Hom[ F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ][ xᴰ , Fcᴰ ] ×
              Dᴰ.Hom[ F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ][ xᴰ , Fcᴰ' ]) → _
      goal cone = uniqueExists l reind-l-β
        (λ _ _ _ → isSet× Dᴰ.isSetHomᴰ Dᴰ.isSetHomᴰ _ _ _ _)
        (λ a' x₁ → congS fst (vbp .universalᴰ .equiv-proof reind-cone .snd (a' , subgoal a' x₁)))
        where
        p : F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id
        p = F .F-seq _ _ ∙ congS (λ x₁ → F ⟪ f ⟫ ⋆⟨ D ⟩ x₁) (F .F-id)
        reind-cone : Dᴰ.Hom[ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ][ xᴰ , Fcᴰ ] ×
          Dᴰ.Hom[ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ][ xᴰ , Fcᴰ' ]
        reind-cone .fst = reind p (cone .fst)
        reind-cone .snd = reind p (cone .snd)
        l : Dᴰ.Hom[ F ⟪ f ⟫ ][ xᴰ , vbp .vertexᴰ ]
        l = V.vert-pair (reind-cone .fst) (reind-cone .snd)
        l-β : (l Dᴰ.⋆ᴰ V.vert-π₁ , l Dᴰ.⋆ᴰ V.vert-π₂) ≡ reind-cone
        l-β = vbp .universalᴰ .equiv-proof reind-cone .fst .snd
        reind-l-β : (l Rᴰ.⋆ᴰ reind-π₁₂ .fst ,
                l Rᴰ.⋆ᴰ reind-π₁₂ .snd)
                ≡ cone
        reind-l-β = ≡-×
          (≡[]-rectify (reind-filler-sym _ _ [ _ ]∙[ _ ]
            congP (λ _ x → l Dᴰ.⋆ᴰ x) (reind-filler-sym _ _) [ _ ]∙[ _ ]
            congS fst l-β [ _ ]∙[ _ ]
            reind-filler-sym _ _))
          (≡[]-rectify (reind-filler-sym _ _ [ _ ]∙[ _ ]
            congP (λ _ x → l Dᴰ.⋆ᴰ x) (reind-filler-sym _ _) [ _ ]∙[ _ ]
            congS snd l-β [ _ ]∙[ _ ]
            reind-filler-sym _ _))
        subgoal : (a' : Dᴰ.Hom[ F ⟪ f ⟫ ][ xᴰ , V.vert-cᴰ×cᴰ' ]) →
          (x₁ : (a' Rᴰ.⋆ᴰ reind-π₁₂ .fst , a' Rᴰ.⋆ᴰ reind-π₁₂ .snd) ≡ cone) →
          (a' Dᴰ.⋆ᴰ V.vert-π₁ , a' Dᴰ.⋆ᴰ V.vert-π₂) ≡ reind-cone
        subgoal a' x₁ = ≡-×
          (≡[]-rectify (congP (λ _ x → a' Dᴰ.⋆ᴰ x) (reind-filler _ _) [ _ ]∙[ _ ]
            reind-filler _ _ [ _ ]∙[ _ ]
            congS fst x₁ [ _ ]∙[ _ ]
            reind-filler _ _))
          (≡[]-rectify (congP (λ _ x → a' Dᴰ.⋆ᴰ x) (reind-filler _ _) [ _ ]∙[ _ ]
            reind-filler _ _ [ _ ]∙[ _ ]
            congS snd x₁ [ _ ]∙[ _ ]
            reind-filler _ _))
