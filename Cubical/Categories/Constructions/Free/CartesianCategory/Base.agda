{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Constructions.Free.CartesianCategory.Util
open import Cubical.Categories.Functor
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Data.Equality hiding (id; isProp; Iso)
  renaming ( _≡_ to Eq
           ; refl to reflEq
           ; sym to symEq
           ; _∙_ to _∙Eq_
           ; transport to transportEq
           ; funExt to funExtEq
           )
--open import Cubical.Data.Equality.Conversion renaming (funExt to funExtEq)
open BinaryCartesianCategory
open StrictCartesianFunctor
open Category
open ProductQuiver
open Functor

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  ℓq ℓq' : Level
  ℓc ℓc' : Level
  ℓd ℓd' : Level

module _ (Q : ProductQuiver ℓq ℓq') where
  open import Cubical.Categories.Limits.BinProduct
  open import Cubical.Categories.Limits.BinProduct.More
  open BinProduct
  open Notation

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
  FreeCartesianCategory .prod A B .binProdOb = A ×̬ B
  FreeCartesianCategory .prod A B .binProdPr₁ = π₁ₑ
  FreeCartesianCategory .prod A B .binProdPr₂ = π₂ₑ
  FreeCartesianCategory .prod A B .univProp f g = (⟨ f ,ₑ g ⟩ , ×̬β₁ , ×̬β₂) ,
    λ (h , p , q) →
      λ i → sym (×η-lemma h p q) i , isSet→isSet' isSetEdgeExpr ×̬β₁ p (congS (λ x → x ⋆ₑ π₁ₑ) (sym (×η-lemma h p q))) refl i , isSet→isSet' isSetEdgeExpr ×̬β₂ q (congS (λ x → x ⋆ₑ π₂ₑ) (sym (×η-lemma h p q))) refl i
    where
    -- this direction has more `sym` s, but I like it more 
    ×η-lemma : ∀{A B C f g} → (h : EdgeExpr[ C , A ×̬ B ]) → h ⋆ₑ π₁ₑ ≡ f → h ⋆ₑ π₂ₑ ≡ g → h ≡ ⟨ f ,ₑ g ⟩
    ×η-lemma h p q = (sym ×̬η) ∙ cong₂ (λ x y → ⟨ x ,ₑ y ⟩) p q
  FreeCartesianCategory .⊤ = ⊤̬
  FreeCartesianCategory .! = !ₑ
  FreeCartesianCategory .⊤η = ⊤̬η
  open Interp
  reinterp-trivial : (A : ProdTypeExpr') → Eq (interpret-objects Q FreeCartesianCategory ↑̬ A) A
  reinterp-trivial (↑̬ B) = reflEq
  reinterp-trivial (B ×̬ C) = ap₂ (λ x y → x ×̬ y) (reinterp-trivial B) (reinterp-trivial C)
  reinterp-trivial ⊤̬  = reflEq
  η : Interp Q FreeCartesianCategory
  η .I-ob = ↑̬
  η .I-hom e = transportEq (λ x → EdgeExpr[ x (Q .dom e) , x (Q .cod e) ]) (symEq (funExtEq reinterp-trivial)) (↑ₑ e)
  --η .I-hom e = transport (λ x → EdgeExpr[ x (Q .dom e) , x (Q .cod e) ]) (symEq (funExtEq reinterp-trivial)) (↑ₑ e)
  elimExpProp : ∀{P : ∀{t t'} → FreeCartesianCategory .cat [ t , t' ] → Type ℓ}
      → (∀{t t'} f → isProp (P {t} {t'} f))
      → (∀ e → P (↑ₑ e))
      → (∀{A} → P {A} idₑ)
      → (∀{t t' t''} → ∀ f f' → P {t} {t'} f → P {t'} {t''} f' → P (f ⋆ₑ f'))
      → (∀{A B} → P (π₁ₑ {A} {B}))
      → (∀{A B} → P (π₂ₑ {A} {B}))
      → (∀{A B C} → ∀ f f' → P {C} {A} f → P {C} {B} f' → P ⟨ f ,ₑ f' ⟩)
      → (∀{t} → P (!ₑ {t}))
      → ∀{t t'} f → P {t} {t'} f
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (↑ₑ e) = P↑ e
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! idₑ = Pid
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (f ⋆ₑ f') = P⋆ f f' (elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! f) (elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! f')
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (⋆ₑIdL f i) = {!!}
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (⋆ₑIdR f i) = {!!}
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (⋆ₑAssoc f f' f'' i) = {!!}
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (isSetEdgeExpr f f' p q i j) = {!!}
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! π₁ₑ = Pπ₁
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! π₂ₑ = Pπ₂
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! ⟨ f ,ₑ f₁ ⟩ = {!!}
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! !ₑ = P!
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (×̬β₁ i) = {!!}
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (×̬β₂ i) = {!!}
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (×̬η i) = {!!}
  elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (⊤̬η i) = {!!}
  module _ {𝓒 : BinaryCartesianCategory ℓc ℓc'}(F : StrictCartesianFunctor FreeCartesianCategory 𝓒) where
  module _ {𝓒 : BinaryCartesianCategory ℓc ℓc'}(F F' : StrictCartesianFunctor FreeCartesianCategory 𝓒) where
    module _ (agree-on-η-ob : ∀ v → F .functor ⟅ ↑̬ v ⟆ ≡ F' .functor ⟅ ↑̬ v ⟆) where
      aoo : ∀ t → F .functor ⟅ t ⟆ ≡ F' .functor ⟅ t ⟆
      aoo (↑̬ A) = agree-on-η-ob A
      aoo (A ×̬ B) = F .preserves-× ∙∙ cong₂ (λ x y → x ×⟨ 𝓒 ⟩ y) (aoo A) (aoo B) ∙∙ sym (F' .preserves-×)
      aoo ⊤̬ = F .preserves-⊤ ∙ sym (F' .preserves-⊤)
      module _ (agree-on-η-hom : ∀ e → PathP (λ i → cong₂ (λ x y → 𝓒 .cat [ x , y ]) (aoo (Q .dom e)) (aoo (Q .cod e)) i) (F .functor ⟪ ↑ₑ e ⟫) (F' .functor ⟪ ↑ₑ e ⟫)) where
        module _ {t t'}(f : FreeCartesianCategory .cat [ t , t' ]) where
          open import Cubical.Foundations.HLevels
          open import Cubical.Foundations.Path
          open import Cubical.Foundations.Isomorphism
          open Iso
          aom-type : Type _
          aom-type = PathP (λ i → cong₂ (λ x y → 𝓒 .cat [ x , y ]) (aoo t) (aoo t') i) (F .functor .F-hom f) (F' .functor .F-hom f)
          isProp-aom-type : isProp aom-type
          isProp-aom-type = isPropRetract fromPathP toPathP (PathPIsoPath _ _ _ .leftInv) (𝓒 .cat .isSetHom _ _)
        aom : ∀{t t'}(f : FreeCartesianCategory .cat [ t , t' ]) → aom-type f
        aom f = elimExpProp {P = aom-type}
          isProp-aom-type
          agree-on-η-hom
          (F .functor .F-id ◁ (λ i → 𝓒 .cat .id) ▷ sym (F' .functor .F-id))
          (λ f₁ f₂ p q → F .functor .F-seq f₁ f₂ ◁ (λ i → p i ⋆⟨ 𝓒 .cat ⟩ q i) ▷ sym (F' .functor .F-seq f₁ f₂))
          {!!}
          {!!}
          (λ f₁ f₂ p q → {!!})
          ({!!} ◁ {!!} ▷ {!!})
          {!!}
        ind : F .functor ≡ F' .functor
        ind = Functor≡ aoo aom
