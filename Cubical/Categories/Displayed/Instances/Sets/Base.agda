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
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}(Cᴰ : Categoryᴰ C ℓC ℓC')(Dᴰ : Categoryᴰ D ℓD ℓD') where
  open Categoryᴰ
  open NatTransᴰ
  open NatTrans
  open Functor
  -- record modules
  module Cᴰ = Categoryᴰ Cᴰ
  module Dᴰ = Categoryᴰ Dᴰ
  module D = Category D
  idTransᴰ : (F : Functor C D)(Fᴰ : Functorᴰ F Cᴰ Dᴰ) → NatTransᴰ (idTrans F) Fᴰ Fᴰ
  idTransᴰ F Fᴰ .N-obᴰ {x = c} cᴰ = Dᴰ .idᴰ
  --compPathP' (Dᴰ .⋆IdRᴰ (Fᴰ .F-homᴰ fᴰ)) (symP (Dᴰ .⋆IdLᴰ (Fᴰ .F-homᴰ fᴰ)))
  idTransᴰ F Fᴰ .N-homᴰ {x = c} {y = c'} {f = f} {xᴰ = cᴰ} {yᴰ = c'ᴰ} fᴰ = goal
    where
    one : ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (Dᴰ .idᴰ)) Dᴰ.≡[ D.⋆IdR _ ] (Fᴰ .F-homᴰ fᴰ)
    one = Dᴰ .⋆IdRᴰ (Fᴰ .F-homᴰ fᴰ)
    two : ((Dᴰ .idᴰ) Dᴰ.⋆ᴰ (Fᴰ .F-homᴰ fᴰ)) Dᴰ.≡[ D.⋆IdL _ ] (Fᴰ .F-homᴰ fᴰ)
    two = Dᴰ .⋆IdLᴰ (Fᴰ .F-homᴰ fᴰ)
    -- this is the actual proof we need to be displayed over
    theirsD : (F .F-hom f) D.⋆ (D .id) ≡ (D .id) D.⋆ (F .F-hom f)
    theirsD = idTrans F .N-hom f
    -- which is not the same as this proof, for example
    mineD : (F .F-hom f) D.⋆ (D .id) ≡ (D .id) D.⋆ (F .F-hom f)
    mineD = (D.⋆IdR _) ∙ (sym (D.⋆IdL _))
    -- but it doesn't really matter since homsets are sets, so we can transport
    sameMineTheirsD : mineD ≡ theirsD
    sameMineTheirsD = D.isSetHom _ _ _ _
    mineDᴰ : PathP (λ i →
              ((cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (D.⋆IdR _))
              ∙
              (cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (sym (D.⋆IdL _))))
              i)
            ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (Dᴰ .idᴰ))
            ((Dᴰ .idᴰ) Dᴰ.⋆ᴰ (Fᴰ .F-homᴰ fᴰ))
    mineDᴰ = compPathP one (symP two)
    ten : Dᴰ.Hom[ (F .F-hom f) D.⋆ (D .id) ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]
            ≡
            Dᴰ.Hom[ (D .id) D.⋆ (F .F-hom f) ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]
    ten = ((cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (D.⋆IdR (F .F-hom f)))
            ∙
            (cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (sym (D.⋆IdL (F .F-hom f)))))
    ten' : Dᴰ.Hom[ F .F-hom f D.⋆ D .id ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]
          ≡
             Dᴰ.Hom[ D .id D.⋆ F .F-hom f ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]
    ten' = cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) theirsD
    --hard : isProp (Dᴰ.Hom[ F .F-hom f D.⋆ D .id ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]
    --          ≡
    --         Dᴰ.Hom[ D .id D.⋆ F .F-hom f ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ])
    --hard p q = {!isSet→SquareP (λ _ _ → Dᴰ.isSetHomᴰ) p!}
    need' : ((cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (D.⋆IdR (F .F-hom f)))
              ∙
              (cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (sym (D.⋆IdL (F .F-hom f)))))
              ≡
              cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (((D.⋆IdR (F .F-hom f))) ∙ (sym (D.⋆IdL (F .F-hom f))))
    need' = sym (cong-∙ ((λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ])) ((D.⋆IdR (F .F-hom f))) ((sym (D.⋆IdL (F .F-hom f)))))
    need : ((cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (D.⋆IdR (F .F-hom f)))
              ∙
              (cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (sym (D.⋆IdL (F .F-hom f)))))
            ≡
            cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) theirsD
    need = need' ∙ congS
                     (λ y → cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) y)
                     (D .isSetHom _ _ _ _)
    --four : ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (Dᴰ .idᴰ)) Dᴰ.≡[ mineD ] ((Dᴰ .idᴰ) Dᴰ.⋆ᴰ (Fᴰ .F-homᴰ fᴰ))
    --four = {!mineDᴰ!}
    --fob : {A : Type ℓ}{B : A → Type ℓ}{x y z : A}(f : (a : A) → B a)(p : x ≡ y)(q : y ≡ z) →
    --  (cong f (p ∙ q)) ≡ ((cong f p) ∙ (cong f q))
    --flib :
    --          cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (D.⋆IdR (F .F-hom f) ∙ sym (D.⋆IdL (F .F-hom f)))
    --          ≡
    --          (cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (D.⋆IdR (F .F-hom f))
    --          ∙
    --          (cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (sym (D.⋆IdL (F .F-hom f)))))
    --flib = {!!}
    five : PathP (λ i →
              ((cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (D.⋆IdR (F .F-hom f)))
              ∙
              (cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) (sym (D.⋆IdL (F .F-hom f)))))
              i)
            ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (Dᴰ .idᴰ))
            ((Dᴰ .idᴰ) Dᴰ.⋆ᴰ (Fᴰ .F-homᴰ fᴰ))
          ≡
          PathP (λ i → cong (λ x → Dᴰ.Hom[ x ][ Fᴰ .F-obᴰ cᴰ , Fᴰ .F-obᴰ c'ᴰ ]) theirsD i)
            ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (Dᴰ .idᴰ))
            ((Dᴰ .idᴰ) Dᴰ.⋆ᴰ (Fᴰ .F-homᴰ fᴰ))
    five = cong (λ x → PathP (λ i → x i)
      ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (Dᴰ .idᴰ)) ((Dᴰ .idᴰ) Dᴰ.⋆ᴰ (Fᴰ .F-homᴰ fᴰ)))
      need
    -- we want the naturality square to be displayed over their proof
    goal : ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (Dᴰ .idᴰ)) Dᴰ.≡[ theirsD ] ((Dᴰ .idᴰ) Dᴰ.⋆ᴰ (Fᴰ .F-homᴰ fᴰ))
    goal = transport five mineDᴰ

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
    --baz : PathP (λ k → (PathP (λ j → Dᴰ [ (α≡β k) .N-hom f j ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ])
    --        ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ ((aoc k) c'ᴰ))
    --        (((aoc k) cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ)))) foo bar
    --baz = {!!}
    --remᴰ : PathP
    --  (λ k → (PathP
    --    (λ j → Dᴰ [ (α≡β k) .N-hom f j ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ])
    --    ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ ((aoc k) c'ᴰ))
    --    (((aoc k) cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ))))
    --  (αᴰ .N-homᴰ fᴰ)
    --  (βᴰ .N-homᴰ fᴰ)
    --remᴰ = (isSet→SquareP (λ _ _ → {!Dᴰ .isSetHomᴰ!}) foo bar {!cong (λ x → Dᴰ ._⋆ᴰ_ (Fᴰ .F-homᴰ fᴰ) (x c'ᴰ)) aoc!} {!cong (λ x → Dᴰ ._⋆ᴰ_ (x cᴰ) (Gᴰ .F-homᴰ fᴰ)) aoc!})

  --idLTransᴰ : {F G : Functor C D}{α : NatTrans F G}{Fᴰ : Functorᴰ F Cᴰ Dᴰ}{Gᴰ : Functorᴰ G Cᴰ Dᴰ}(αᴰ : NatTransᴰ α Fᴰ Gᴰ) →
  --  --PathP (λ i → NatTransᴰ (FUNCTOR C D .⋆IdL α i) Fᴰ Gᴰ)
  --  PathP (λ i → {!!} i)
  --  (seqTransᴰ (idTransᴰ F Fᴰ) αᴰ) αᴰ
  --idLTransᴰ = {!!}
  --FUNCTORᴰ : Categoryᴰ (FUNCTOR C D)  _ _
  --FUNCTORᴰ .ob[_] F = Functorᴰ F Cᴰ Dᴰ
  --FUNCTORᴰ .Hom[_][_,_] {x = F} {y = G} α Fᴰ Gᴰ = NatTransᴰ α Fᴰ Gᴰ
  --FUNCTORᴰ .idᴰ {x = F} {p = Fᴰ} = idTransᴰ F Fᴰ
  --FUNCTORᴰ ._⋆ᴰ_ {x = F} {y = G} {z = H} {f = α} {g = β} {xᴰ = Fᴰ} {yᴰ = Gᴰ} {zᴰ = Hᴰ} αᴰ βᴰ = seqTransᴰ αᴰ βᴰ
  --FUNCTORᴰ .⋆IdLᴰ {x = F} {y = G} {f = α} {xᴰ = Fᴰ} {yᴰ = Gᴰ} αᴰ = idLTransᴰ {!!}
