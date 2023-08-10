{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
open import Cubical.Categories.Functor
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Categories.Constructions.Free.Cartesian.Util
open import Cubical.Categories.Constructions.Free.Cartesian.Data

open Category
open Functor
open BinaryCartesianCategory
open StrictCartesianFunctor
open ProductQuiver
module _ (Q : ProductQuiver ℓq ℓq') where
  private variable ℓ ℓ' ℓ'' ℓ''' : Level
  private variable ℓq ℓq' : Level
  private variable ℓc ℓc' : Level
  private variable ℓd ℓd' : Level
  open import Cubical.Categories.Limits.BinProduct
  open BinProduct
  open import Cubical.Data.Sigma.Base
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
  open import Cubical.Categories.Limits.BinProduct.More
  open Notation
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
  FreeCartesianCategory .prod A B .univProp f g =
    (⟨ f ,ₑ g ⟩ , ×̬β₁ , ×̬β₂) , λ (h , p , q) →
    λ i → sym (×η-lemma h p q) i , isSet→isSet' isSetEdgeExpr ×̬β₁ p (congS (λ x → x ⋆ₑ π₁ₑ) (sym (×η-lemma h p q))) refl i , isSet→isSet' isSetEdgeExpr ×̬β₂ q (congS (λ x → x ⋆ₑ π₂ₑ) (sym (×η-lemma h p q))) refl i
    where
    ×η-lemma : ∀{A B C f g} → (h : EdgeExpr[ C , A ×̬ B ]) → h ⋆ₑ π₁ₑ ≡ f → h ⋆ₑ π₂ₑ ≡ g → h ≡ ⟨ f ,ₑ g ⟩
    ×η-lemma h p q = (sym ×̬η) ∙ congS₂ (λ x y → ⟨ x ,ₑ y ⟩) p q
  FreeCartesianCategory .⊤ = ⊤̬
  FreeCartesianCategory .! = !ₑ
  FreeCartesianCategory .⊤η = ⊤̬η
  open Interp
  reinterp-trivial : (A : ProdTypeExpr') → interpret-objects Q FreeCartesianCategory ↑̬ A ≡ A
  reinterp-trivial (↑̬ B) = refl
  reinterp-trivial (B ×̬ C) i = reinterp-trivial B i ×̬ reinterp-trivial C i
  reinterp-trivial ⊤̬  = refl
  reinterp-trivial' : _
  reinterp-trivial' = funExt reinterp-trivial
  η : Interp Q FreeCartesianCategory
  η .I-ob = ↑̬
  η .I-hom e = transport⁻ inside-EdgeExpr (↑ₑ e)
    where
    inside-EdgeExpr : ∀{A B} → EdgeExpr[ interpret-objects Q FreeCartesianCategory ↑̬ A , interpret-objects Q FreeCartesianCategory ↑̬ B ] ≡ EdgeExpr[ A , B ]
    inside-EdgeExpr {A} {B} = congS (λ x → EdgeExpr[ x A , x B ]) reinterp-trivial'
  module _ {𝓒 : BinaryCartesianCategory ℓc ℓc'}(F : StrictCartesianFunctor FreeCartesianCategory 𝓒) where
    --a : {e : Q .edge} → 𝓒 .cat [ F .functor ⟅ interpret-objects Q FreeCartesianCategory ↑̬ (Q .dom e) ⟆ , F .functor ⟅ interpret-objects Q FreeCartesianCategory ↑̬ (Q .cod e) ⟆ ]
    --a {e = e} = F .functor ⟪ η .I-hom e ⟫
    --b : {e : Q .edge} → 𝓒 .cat [ F .functor ⟅ Q .dom e ⟆ , F .functor ⟅ Q .cod e ⟆ ]
    --b {e = e} = F .functor ⟪ ↑ₑ e ⟫
    F⟪η⟫ : ∀ e → _
    F⟪η⟫ e = F .functor ⟪ η .I-hom e ⟫
    F⟪↑⟫ : ∀ e → _
    F⟪↑⟫ e = F .functor ⟪ ↑ₑ e ⟫
    F⟪η⟫≡F⟪↑⟫-Hom-lem : _
    F⟪η⟫≡F⟪↑⟫-Hom-lem = congS (λ x → ∀ e → 𝓒 .cat [ F .functor ⟅ x (Q .dom e) ⟆ , F .functor ⟅ x (Q .cod e) ⟆ ]) reinterp-trivial'
    F⟪η⟫≡F⟪↑⟫-Hom : PathP (λ i → F⟪η⟫≡F⟪↑⟫-Hom-lem i) F⟪η⟫ F⟪↑⟫
    F⟪η⟫≡F⟪↑⟫-Hom = funExt λ e → congP (λ i a → F .functor ⟪ a ⟫) (toPathP⁻ refl)
  module _ {𝓒 : BinaryCartesianCategory ℓc ℓc'}(F F' : StrictCartesianFunctor FreeCartesianCategory 𝓒) where
    module _ (agree-on-η : F ∘I η ≡ F' ∘I η) where
      open import Cubical.Foundations.HLevels
      open import Cubical.Foundations.Path
      open import Cubical.Foundations.Isomorphism
      open Iso
      ttt : ∀ t → F .functor ⟅ interpret-objects Q FreeCartesianCategory (η .I-ob) t ⟆ ≡ F .functor ⟅ t ⟆
      ttt t = congS (λ x → F .functor ⟅ x t ⟆) reinterp-trivial'
      aoo : ∀ t → F .functor ⟅ t ⟆ ≡ F' .functor ⟅ t ⟆
      aoo (↑̬ A) i = agree-on-η i .I-ob A
      aoo (A ×̬ B) = F .preserves-× ∙∙ inside-× 𝓒 (aoo A) (aoo B) ∙∙ sym (F' .preserves-×)
      -- F .preserves-× ∙ inside-× 𝓒 (aoo A) (aoo B) ∙ sym (F' .preserves-×)
      aoo ⊤̬ = F .preserves-⊤ ∙ sym (F' .preserves-⊤)
      aoo' = funExt aoo
      aom-type : ∀{t t'} → (f : FreeCartesianCategory .cat [ t , t' ]) → Type _
      aom-type {t} {t'} f = PathP (λ i → congS (λ x → 𝓒 .cat [ x t , x t' ]) aoo' i) (F .functor .F-hom f) (F' .functor .F-hom f)
      -- mnemonic
      F⟪-⟫≡F'⟪-⟫ = aom-type
      -- c/p Cubical.Categories.Constructions.Free.Category proof
      isProp-aom-type : ∀{t t'} → (f : FreeCartesianCategory .cat [ t , t' ]) → isProp (F⟪-⟫≡F'⟪-⟫ f)
      isProp-aom-type f = isPropRetract fromPathP toPathP (PathPIsoPath _ _ _ .leftInv) (𝓒 .cat .isSetHom _ _)
      F⟪η⟫≡F'⟪η⟫-Hom : _
      F⟪η⟫≡F'⟪η⟫-Hom = F⟪ı⟫≡G⟪ı⟫-Hom F F' η agree-on-η
      F⟪↑⟫≡F'⟪↑⟫ : PathP
                     (λ i →
                        ((λ i₁ → F⟪η⟫≡F⟪↑⟫-Hom-lem F (~ i₁)) ∙∙
                         (λ i₁ → F⟪ı⟫≡G⟪ı⟫-Hom-lem F F' η agree-on-η i₁) ∙∙
                         (λ i₁ → F⟪η⟫≡F⟪↑⟫-Hom-lem F' i₁))
                        i)
                     (F⟪↑⟫ F) (F⟪↑⟫ F')
      F⟪↑⟫≡F'⟪↑⟫ = doubleCompP' _ _ _
        (symP-fromGoal (F⟪η⟫≡F⟪↑⟫-Hom F)) (F⟪η⟫≡F'⟪η⟫-Hom) (F⟪η⟫≡F⟪↑⟫-Hom F')
      F⟪↑⟫≡F'⟪↑⟫' : _
      F⟪↑⟫≡F'⟪↑⟫' = cong-transport-PathP (symP (transport (PathP≡doubleCompPathˡ (F⟪η⟫≡F⟪↑⟫-Hom-lem F) (F⟪ı⟫≡G⟪ı⟫-Hom-lem F F' η agree-on-η) {!!} (F⟪η⟫≡F⟪↑⟫-Hom-lem F')) {!!})) (symP-fromGoal (F⟪η⟫≡F⟪↑⟫-Hom F) ⋆⋆ F⟪η⟫≡F'⟪η⟫-Hom ⋆⋆ F⟪η⟫≡F⟪↑⟫-Hom F')
      abcbc : PathP
                (λ i →
                   ((λ i₁ → F⟪η⟫≡F⟪↑⟫-Hom-lem F (~ i₁)) ∙∙
                    (λ i₁ → F⟪ı⟫≡G⟪ı⟫-Hom-lem F F' η agree-on-η i₁) ∙∙
                    (λ i₁ → F⟪η⟫≡F⟪↑⟫-Hom-lem F' i₁))
                   i)
                (F⟪↑⟫ F) (F⟪↑⟫ F')
      abcbc =  (symP-fromGoal (F⟪η⟫≡F⟪↑⟫-Hom F) ⋆⋆ F⟪η⟫≡F'⟪η⟫-Hom ⋆⋆ F⟪η⟫≡F⟪↑⟫-Hom F')
      F⟪↑⟫≡F'⟪↑⟫'' : (e : Q .edge) → {!!}
      -- why can't I get congP to work??
      F⟪↑⟫≡F'⟪↑⟫'' = funExt⁻ {!!}
      aom-base-case : ∀ e → F⟪-⟫≡F'⟪-⟫ (↑ₑ e)
      --bruh e = cong-transport-PathP {!!} (F⟪↑⟫≡F'⟪↑⟫)
      aom-base-case e = {!!}
      --foo : ∀ e
      --  → congS₂ (λ x y → 𝓒 .cat [ x , y ]) (aoo (Q .dom e)) (aoo (Q .cod e))
      --  ≡ (sym
      --  (congS₂ (λ x y → 𝓒 .cat [ F .functor ⟅ x ⟆ , F .functor ⟅ y ⟆ ]) (reinterp-trivial (Q .dom e)) (reinterp-trivial (Q .cod e))))
      --  ∙∙ (F⟪ı⟫≡G⟪ı⟫-Hom-lem F F' η agree-on-η)
      --  ∙∙ (congS₂ (λ x y → 𝓒 .cat [ F' .functor ⟅ x ⟆ , F' .functor ⟅ y ⟆ ]) (reinterp-trivial (Q .dom e)) (reinterp-trivial (Q .cod e)))
      --foo e = sym (transport (PathP≡doubleCompPathˡ ((congS₂ (λ x y → 𝓒 .cat [ F .functor ⟅ x ⟆ , F .functor ⟅ y ⟆ ]) (reinterp-trivial (Q .dom e)) (reinterp-trivial (Q .cod e)))) ((F⟪ı⟫≡G⟪ı⟫-Hom-lem F F' η agree-on-η)) (congS₂ (λ x y → 𝓒 .cat [ x , y ]) (aoo (Q .dom e)) (aoo (Q .cod e))) ((congS₂ (λ x y → 𝓒 .cat [ F' .functor ⟅ x ⟆ , F' .functor ⟅ y ⟆ ]) (reinterp-trivial (Q .dom e)) (reinterp-trivial (Q .cod e))))) {!!})
      --bruh e = cong-transport-PathP {!!} (symP (F⟪η⟫≡F⟪↑⟫-Hom F {e = e}) ⋆⋆ F⟪ı⟫≡G⟪ı⟫-Hom {Q = Q} {𝓒 = FreeCartesianCategory} {𝓓 = 𝓒} F F' η agree-on-η {e = e} ⋆⋆ F⟪η⟫≡F⟪↑⟫-Hom F' {e = e})
      --bruh e = cong-transport-PathP {!!} (symP (F⟪η⟫≡F⟪↑⟫-Hom F {e = e}) ⋆⋆ F⟪ı⟫≡G⟪ı⟫-Hom {Q = Q} {𝓒 = FreeCartesianCategory} {𝓓 = 𝓒} F F' η agree-on-η {e = e} ⋆⋆ F⟪η⟫≡F⟪↑⟫-Hom F' {e = e})
      aom : ∀{t t'} → (f : FreeCartesianCategory .cat [ t , t' ]) → F⟪-⟫≡F'⟪-⟫ f
      --aom = elimExpProp {P = F⟪-⟫≡F'⟪-⟫} isProp-aom-type (λ e → {!F⟪ı⟫≡G⟪ı⟫-Hom F F' η agree-on-η {e = e}!}) {!!} {!!} {!!} {!!} {!!} {!!}
      aom = elimExpProp {P = F⟪-⟫≡F'⟪-⟫} isProp-aom-type
        --(λ e → toPathP (congS (λ x → {!!}) (fromPathP (symP (F⟪η⟫≡F⟪↑⟫-Hom F) ⋆⋆ F⟪ı⟫≡G⟪ı⟫-Hom {Q = Q} {𝓒 = FreeCartesianCategory} {𝓓 = 𝓒} F F' η agree-on-η {e = e} ⋆⋆ F⟪η⟫≡F⟪↑⟫-Hom F'))))
        --(λ e → cong-transport-PathP {!!} (symP (F⟪η⟫≡F⟪↑⟫-Hom F {e = e}) ⋆⋆ F⟪ı⟫≡G⟪ı⟫-Hom {Q = Q} {𝓒 = FreeCartesianCategory} {𝓓 = 𝓒} F F' η agree-on-η {e = e} ⋆⋆ F⟪η⟫≡F⟪↑⟫-Hom F' {e = e}))
        (λ e → {!!})
        --(fromPathP (symP (F⟪η⟫≡F⟪↑⟫-Hom F) ⋆⋆ F⟪ı⟫≡G⟪ı⟫-Hom {Q = Q} {𝓒 = FreeCartesianCategory} {𝓓 = 𝓒} F F' η agree-on-η {e = e} ⋆⋆ F⟪η⟫≡F⟪↑⟫-Hom F')))
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        where
        -- prove a proposition by induction over the FreeCartesianCategory
        -- so we can ignore higher path coherences in the FreeCartesianCategory
        elimExpProp : ∀{P : ∀{t t'} → FreeCartesianCategory .cat [ t , t' ] → Type ℓ}
          → (∀{t t'} f → isProp (P {t} {t'} f))
          → (∀ e → P (↑ₑ e))
          → (∀{A} → P {A} idₑ)
          → (∀{t t' t'' f f'} → P {t} {t'} f → P {t'} {t''} f' → P (f ⋆ₑ f'))
          → (∀{A B} → P (π₁ₑ {A} {B}))
          → (∀{A B} → P (π₂ₑ {A} {B}))
          → (∀{A B C f g} → P {C} {A} (f) → P {C} {B} (g) → P ⟨ f ,ₑ g ⟩)
          → (∀{t} → P (!ₑ {t}))
          → ∀{t t'} f → P {t} {t'} f
        elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (↑ₑ e) = P↑ e
        elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! idₑ = Pid
        elimExpProp isPropP P↑ Pid P⋆ Pπ₁ Pπ₂ P⟨,⟩ P! (f ⋆ₑ f') = P⋆ {!!} {!!}
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
      -- no need to show F ≡ F' as StrictCartesianFunctor s
      -- (and in fact I think we'd need that isSet (𝓒 .ob))
      ind : F .functor ≡ F' .functor
      ind = Functor≡ aoo {!!} --aom
