{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Sets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓC ℓC' ℓD ℓD' : Level

module _ ℓ ℓ' where
  open Categoryᴰ
  SETᴰ : Categoryᴰ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  SETᴰ .ob[_] X = ⟨ X ⟩ → hSet ℓ'
  SETᴰ .Hom[_][_,_] f P Q = ∀ x → ⟨ P x ⟩ → ⟨ Q (f x) ⟩
  SETᴰ .idᴰ = λ x z → z
  SETᴰ ._⋆ᴰ_ {f = f} {g} fᴰ gᴰ x p = gᴰ (f x) (fᴰ x p)
  SETᴰ .⋆IdLᴰ fᴰ = refl
  SETᴰ .⋆IdRᴰ fᴰ = refl
  SETᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = refl
  SETᴰ .isSetHomᴰ {yᴰ = Q} = isSetΠ λ x → isSetΠ λ xᴰ → Q _ .snd

open Category
open Functorᴰ
-- Displayed representable
_[-][-,_] : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → {c : C .ob}
          → Categoryᴰ.ob[_] D c
          → Functorᴰ (C [-, c ]) (D ^opᴰ) (SETᴰ ℓC' ℓD')
_[-][-,_] {C = C} D {c} d .F-obᴰ d' f =
  (D [ f ][ d' , d ]) , Categoryᴰ.isSetHomᴰ D
_[-][-,_] {C = C} D {c} d .F-homᴰ fᴰ g gᴰ = Categoryᴰ._⋆ᴰ_ D fᴰ gᴰ
_[-][-,_] {C = C} D {c} d .F-idᴰ i g gᴰ = Categoryᴰ.⋆IdLᴰ D gᴰ i
_[-][-,_] {C = C} D {c} d .F-seqᴰ fᴰ gᴰ i h hᴰ = Categoryᴰ.⋆Assocᴰ D gᴰ fᴰ hᴰ i

-- Displayed representable
_[-][_,-] : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → {c : C .ob}
          → Categoryᴰ.ob[_] D c
          → Functorᴰ (C [ c ,-]) D (SETᴰ ℓC' ℓD')
(D [-][ d ,-]) .F-obᴰ d' f = (D [ f ][ d , d' ]) , Categoryᴰ.isSetHomᴰ D
(D [-][ d ,-]) .F-homᴰ fᴰ g gᴰ = Categoryᴰ._⋆ᴰ_ D gᴰ fᴰ
(D [-][ d ,-]) .F-idᴰ i f fᴰ = Categoryᴰ.⋆IdRᴰ D fᴰ i
(D [-][ d ,-]) .F-seqᴰ fᴰ gᴰ i h hᴰ = Categoryᴰ.⋆Assocᴰ D hᴰ fᴰ gᴰ (~ i)

  --SETᴰ : Categoryᴰ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  --SETᴰ .ob[_] X = ⟨ X ⟩ → hSet ℓ'
  --SETᴰ .Hom[_][_,_] f P Q = ∀ x → ⟨ P x ⟩ → ⟨ Q (f x) ⟩
  --SETᴰ .idᴰ = λ x z → z
  --SETᴰ ._⋆ᴰ_ {f = f} {g} fᴰ gᴰ x p = gᴰ (f x) (fᴰ x p)
  --SETᴰ .⋆IdLᴰ fᴰ = refl
  --SETᴰ .⋆IdRᴰ fᴰ = refl
  --SETᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = refl
  --SETᴰ .isSetHomᴰ {yᴰ = Q} = isSetΠ λ x → isSetΠ λ xᴰ → Q _ .snd
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Functor
open import Cubical.Foundations.GroupoidLaws
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}(Cᴰ : Categoryᴰ C ℓC ℓC')(Dᴰ : Categoryᴰ D ℓD ℓD') where
  open Categoryᴰ
  open NatTransᴰ
  open NatTrans
  open Functor
  open import Cubical.Categories.Displayed.Reasoning Dᴰ
  -- record modules
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    module C = Category C
    module D = Category D
  -- TODO: 3/27 Meeting
  idTransᴰ : (F : Functor C D)(Fᴰ : Functorᴰ F Cᴰ Dᴰ) → NatTransᴰ (idTrans F) Fᴰ Fᴰ
  idTransᴰ F Fᴰ .N-obᴰ {x = c} cᴰ = Dᴰ .idᴰ
  idTransᴰ F Fᴰ .N-homᴰ {x = c} {y = c'} {f = f} {xᴰ = cᴰ} {yᴰ = c'ᴰ} fᴰ = ≡[]-rectify (Dᴰ .⋆IdRᴰ _ [ _ ]∙[ _ ] symP (Dᴰ .⋆IdLᴰ _))

  module _ {F G : Functor C D}{α : NatTrans F G}{Fᴰ : Functorᴰ F Cᴰ Dᴰ}{Gᴰ : Functorᴰ G Cᴰ Dᴰ} where
    open import Cubical.Foundations.Isomorphism
    open Iso
    NatTransᴰΣ : Type _
    NatTransᴰΣ = Σ[ ob ∈ ({c : C .ob} (cᴰ : Cᴰ.ob[ c ]) → Dᴰ.Hom[ α .N-ob c ][ (Fᴰ .F-obᴰ cᴰ) , (Gᴰ .F-obᴰ cᴰ) ]) ]
                    ({c : C.ob} {c' : C.ob} {f : C [ c , c' ]} {cᴰ : Cᴰ.ob[ c ] } {c'ᴰ : Cᴰ.ob[ c' ] } (fᴰ : Cᴰ.Hom[ f ][ cᴰ , c'ᴰ ]) → PathP (λ i → Dᴰ.Hom[ α .N-hom f i ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ]) (Fᴰ .F-homᴰ fᴰ Dᴰ.⋆ᴰ ob c'ᴰ) (ob cᴰ Dᴰ.⋆ᴰ Gᴰ .F-homᴰ fᴰ))
    NatTransIsoᴰΣ : Iso (NatTransᴰ α Fᴰ Gᴰ) NatTransᴰΣ
    NatTransIsoᴰΣ .fun αᴰ = αᴰ .N-obᴰ , αᴰ .N-homᴰ
    NatTransIsoᴰΣ .inv (ob , hom) .N-obᴰ = ob
    NatTransIsoᴰΣ .inv (ob , hom) .N-homᴰ = hom
    NatTransIsoᴰΣ .rightInv _ = refl
    NatTransIsoᴰΣ .leftInv _ = refl
    isSetNatTransᴰ : isSet (NatTransᴰ α Fᴰ Gᴰ)
    isSetNatTransᴰ = isSetRetract (NatTransIsoᴰΣ .fun) (NatTransIsoᴰΣ .inv) (NatTransIsoᴰΣ .leftInv)
      --(isSetΣSndProp (isSetImplicitΠ λ x → isSetΠ (λ xᴰ → Dᴰ .isSetHomᴰ)) (λ b₁ → isPropImplicitΠ4 λ a₁ a₂ a₃ a₄ → isPropImplicitΠ λ x₂ → isPropΠ λ x₃ → {!Dᴰ .isSetHomᴰ!}))
      (isSetΣSndProp (isSetImplicitΠ (λ c → isSetΠ (λ cᴰ → Dᴰ .isSetHomᴰ)))
        λ α-components → isPropImplicitΠ3 λ c c' f → isPropImplicitΠ2 (λ cᴰ c'ᴰ → isPropΠ λ fᴰ → λ p q → isSet→SquareP (λ _ _ → Dᴰ .isSetHomᴰ) _ _ _ _))

  makeNatTransPathᴰ : {F G : Functor C D}{α β : NatTrans F G}{Fᴰ : Functorᴰ F Cᴰ Dᴰ}{Gᴰ : Functorᴰ G Cᴰ Dᴰ}{αᴰ : NatTransᴰ α Fᴰ Gᴰ}{βᴰ : NatTransᴰ β Fᴰ Gᴰ} →
    (α≡β : α ≡ β) →
    (aoc : PathP (λ i → {c : C .ob}(cᴰ : Cᴰ.ob[ c ]) → Dᴰ.Hom[ (α≡β i) .N-ob c ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ cᴰ ]) (αᴰ .N-obᴰ) (βᴰ .N-obᴰ)) →
    PathP (λ i → NatTransᴰ (α≡β i) Fᴰ Gᴰ) αᴰ βᴰ
  makeNatTransPathᴰ α≡β aoc i .N-obᴰ {x = c} cᴰ = (aoc i) cᴰ -- this is η-expanded for clarity
  makeNatTransPathᴰ {F = F} {G = G} {α = α} {β = β} {Fᴰ = Fᴰ} {Gᴰ = Gᴰ} {αᴰ = αᴰ} {βᴰ = βᴰ} α≡β aoc i .N-homᴰ {x = c} {y = c'} {f = f} {xᴰ = cᴰ} {yᴰ = c'ᴰ} fᴰ = remᴰ i
    where
    left : PathP (λ j → Dᴰ [ α .N-hom f j ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ])
            ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (αᴰ .N-obᴰ c'ᴰ))
            ((αᴰ .N-obᴰ cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ))
    left = αᴰ .N-homᴰ fᴰ
    right : PathP (λ j → Dᴰ [ β .N-hom f j ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ])
            ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (βᴰ .N-obᴰ c'ᴰ))
            ((βᴰ .N-obᴰ cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ))
    right = βᴰ .N-homᴰ fᴰ
    top : PathP _
          ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (αᴰ .N-obᴰ c'ᴰ))
          ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (βᴰ .N-obᴰ c'ᴰ))
    top = congP (λ _ x → (Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (x c'ᴰ)) aoc
    bottom : PathP _
             ((αᴰ .N-obᴰ cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ))
             ((βᴰ .N-obᴰ cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ))
    bottom = congP (λ _ x → (x cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ)) aoc
    remᴰ : PathP (λ k →
             PathP (λ j → Dᴰ.Hom[ ((α≡β k) .N-hom f j) ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ])
               ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ ((aoc k) c'ᴰ))
               (((aoc k) cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ)))
           (αᴰ .N-homᴰ fᴰ)
           (βᴰ .N-homᴰ fᴰ)
    remᴰ = isSet→SquareP (λ _ _ → Dᴰ.isSetHomᴰ) left right top bottom

  idLTransᴰ : {F G : Functor C D}{α : NatTrans F G}{Fᴰ : Functorᴰ F Cᴰ Dᴰ}{Gᴰ : Functorᴰ G Cᴰ Dᴰ}(αᴰ : NatTransᴰ α Fᴰ Gᴰ) →
    PathP (λ i → NatTransᴰ (FUNCTOR C D .⋆IdL α i) Fᴰ Gᴰ)
    (seqTransᴰ (idTransᴰ F Fᴰ) αᴰ)
    αᴰ
  idLTransᴰ {F} {G} {α} {Fᴰ} {Gᴰ} αᴰ = makeNatTransPathᴰ (FUNCTOR C D .⋆IdL α) goal
    where
    goal : PathP (λ i → {c : C .ob} (cᴰ : Cᴰ.ob[ c ]) → Dᴰ.Hom[ D .⋆IdL (α .N-ob c) i ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ cᴰ ])
      (λ xᴰ → (Dᴰ .idᴰ) Dᴰ.⋆ᴰ (αᴰ .N-obᴰ xᴰ))
      (αᴰ .N-obᴰ)
    goal = implicitFunExt (λ {x} → funExt (λ xᴰ → Dᴰ.⋆IdLᴰ _))
  idRTransᴰ : {F G : Functor C D}{α : NatTrans F G}{Fᴰ : Functorᴰ F Cᴰ Dᴰ}{Gᴰ : Functorᴰ G Cᴰ Dᴰ}(αᴰ : NatTransᴰ α Fᴰ Gᴰ) →
    PathP (λ i → NatTransᴰ (FUNCTOR C D .⋆IdR α i) Fᴰ Gᴰ)
    (seqTransᴰ αᴰ (idTransᴰ G Gᴰ)) αᴰ
  idRTransᴰ {F} {G} {α} {Fᴰ} {Gᴰ} αᴰ = makeNatTransPathᴰ (FUNCTOR C D .⋆IdR α) goal
    where
    goal : PathP (λ i → {c : C .ob} (cᴰ : Cᴰ.ob[ c ]) → Dᴰ.Hom[ D .⋆IdR (α .N-ob c) i ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ cᴰ ])
      (λ xᴰ → (αᴰ .N-obᴰ xᴰ) Dᴰ.⋆ᴰ (Dᴰ .idᴰ))
      (αᴰ .N-obᴰ)
    goal = implicitFunExt (λ {x} → funExt (λ xᴰ → Dᴰ.⋆IdRᴰ _))
  -- move to Displayed/NaturalTransformation
  FUNCTORᴰ : Categoryᴰ (FUNCTOR C D)  _ _
  FUNCTORᴰ .ob[_] F = Functorᴰ F Cᴰ Dᴰ
  FUNCTORᴰ .Hom[_][_,_] {x = F} {y = G} α Fᴰ Gᴰ = NatTransᴰ α Fᴰ Gᴰ
  FUNCTORᴰ .idᴰ {x = F} {p = Fᴰ} = idTransᴰ F Fᴰ
  FUNCTORᴰ ._⋆ᴰ_ {x = F} {y = G} {z = H} {f = α} {g = β} {xᴰ = Fᴰ} {yᴰ = Gᴰ} {zᴰ = Hᴰ} αᴰ βᴰ = seqTransᴰ αᴰ βᴰ
  FUNCTORᴰ .⋆IdLᴰ {x = F} {y = G} {f = α} {xᴰ = Fᴰ} {yᴰ = Gᴰ} αᴰ = idLTransᴰ αᴰ
  FUNCTORᴰ .⋆IdRᴰ {x = F} {y = G} {f = α} {xᴰ = Fᴰ} {yᴰ = Gᴰ} αᴰ = idRTransᴰ αᴰ
  -- this is slow
  FUNCTORᴰ .⋆Assocᴰ {x = F} {y = G} {z = H} {w = E} {f = α} {g = β} {h = γ} {xᴰ = Fᴰ} {yᴰ = Gᴰ} {zᴰ = Hᴰ} {wᴰ = Eᴰ} αᴰ βᴰ γᴰ =
    makeNatTransPathᴰ (FUNCTOR C D .⋆Assoc α β γ)
    (implicitFunExt (λ {x} → funExt (λ xᴰ →  Dᴰ .⋆Assocᴰ _ _ _)))
  FUNCTORᴰ .isSetHomᴰ {x = F} {y = G} {f = α} {xᴰ = Fᴰ} {yᴰ = Gᴰ} = isSetNatTransᴰ
