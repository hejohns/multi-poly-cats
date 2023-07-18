{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where
open import Cubical.Foundations.Prelude
private variable ℓ ℓ' ℓ'' ℓ''' : Level
private variable ℓq ℓq' : Level
private variable ℓc ℓc' : Level
private variable ℓd ℓd' : Level
open import Cubical.Categories.Category
open Category
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
open BinaryCartesianCategory
open StrictCartesianFunctor
open import Cubical.Categories.Functor
open Functor
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
module _ where -- helpers
  private variable
      A : Type ℓ
      B : Type ℓ'
      C : Type ℓ''
      D : Type ℓ'''
      a a' : A
      b b' : B
      c c' : C
      d : D
  -- this has to be defined already somewhere... right?
  congS₂ : (f : A → B → C) → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  congS₂ f p q i = f (p i) (q i)
  cong-transport-PathP : {eq₁ eq₂ : A ≡ B} → (eq₂ ≡ eq₁) → (p : PathP (λ i → eq₁ i) a b) → PathP (λ i → eq₂ i) a b
  cong-transport-PathP {a = a} eq₁-₂ p = toPathP ((congS (λ x → transport x a) eq₁-₂) ∙ fromPathP p)
  doubleCompP : {A B C D : Type ℓ} → ∀{a b c d}{eq₁ : A ≡ B}{eq₂ : B ≡ C}{eq₃ : C ≡ D}
    → (p : PathP (λ i → eq₁ i) a b)(q : PathP (λ i → eq₂ i) b c)(r : PathP (λ i → eq₃ i) c d)
    → PathP (λ i → (eq₁ ∙ eq₂ ∙ eq₃) i) a d
  doubleCompP p q r = compPathP p (compPathP q r)
  -- heterogeneous double composition, at the "proper" types
  _⋆⋆_⋆⋆_ : {eq₁ : A ≡ B}{eq₂ : B ≡ C}{eq₃ : C ≡ D}
    → (p : PathP (λ i → eq₁ i) a b)(q : PathP (λ i → eq₂ i) b c)(r : PathP (λ i → eq₃ i) c d)
    → PathP (λ i → (eq₁ ∙∙ eq₂ ∙∙ eq₃) i) a d
  _⋆⋆_⋆⋆_ {a = a} {eq₁ = eq₁} {eq₂ = eq₂} {eq₃ = eq₃} p q r = cong-transport-PathP (doubleCompPath≡compPath eq₁ eq₂ eq₃) (doubleCompP p q r)
  --toPathP ((congS (λ x → transport x a) (doubleCompPath≡compPath eq₁ eq₂ eq₃)) ∙ (fromPathP (doubleCompP p q r)))
module Data where -- generating data
  module _ (Vertex : Type ℓ) where
    data ProdTypeExpr : Type ℓ where
      ↑̬ : Vertex → ProdTypeExpr
      _×̬_ : ProdTypeExpr → ProdTypeExpr → ProdTypeExpr
      ⊤̬ : ProdTypeExpr
  -- TODO: what is going on with these level variables
  record ProductQuiver ℓq ℓq' : Type (ℓ-suc (ℓ-max ℓq ℓq')) where
    field
      vertex : Type ℓq
      edge : Type ℓq'
      dom : edge → ProdTypeExpr vertex
      cod : edge → ProdTypeExpr vertex
  open ProductQuiver
  interpret-objects : (Q : ProductQuiver ℓq ℓq')(𝓒 : BinaryCartesianCategory ℓc ℓc') → (Q .vertex → 𝓒 .cat .ob) → ProdTypeExpr (Q .vertex) → 𝓒 .cat .ob
  interpret-objects Q 𝓒 ı (↑̬ A) = ı A
  interpret-objects Q 𝓒 ı (A ×̬ B) = interpret-objects Q 𝓒 ı A ×⟨ 𝓒 ⟩ interpret-objects Q 𝓒 ı B
  interpret-objects Q 𝓒 ı ⊤̬ = 𝓒 .⊤
  record Interp (Q : ProductQuiver ℓq ℓq')(𝓒 : BinaryCartesianCategory ℓc ℓc') : Type (ℓ-max (ℓ-max ℓq ℓq') (ℓ-max ℓc ℓc')) where
    field
      I-ob : Q .vertex → 𝓒 .cat .ob 
      I-hom : (e : Q .edge) → 𝓒 .cat [ interpret-objects Q 𝓒 I-ob (Q .dom e) , interpret-objects Q 𝓒 I-ob (Q .cod e) ]
  open Interp
  -- helpers
  inside-× : (𝓒 : BinaryCartesianCategory ℓc ℓc') → ∀{A A' B B'} → A ≡ A' → B ≡ B' → A ×⟨ 𝓒 ⟩ B ≡ A' ×⟨ 𝓒 ⟩ B'
  inside-× 𝓒 = congS₂ (λ x y → x ×⟨ 𝓒 ⟩ y)
  module _ {Q : ProductQuiver ℓq ℓq'}{𝓒 : BinaryCartesianCategory ℓc ℓc'}{𝓓 : BinaryCartesianCategory ℓd ℓd'}(F : StrictCartesianFunctor 𝓒 𝓓)(ı : Interp Q 𝓒) where
    -- TODO: this is terrible
    -- hejohns: checked
    F-interp-ob-comm : ∀ t → F .functor ⟅ interpret-objects Q 𝓒 (ı .I-ob) t ⟆ ≡ interpret-objects Q 𝓓 (λ x → F .functor ⟅ ı .I-ob x ⟆) t
    F-interp-ob-comm (↑̬ B) = refl
    F-interp-ob-comm (B ×̬ C) = F .preserves-× ∙ inside-× 𝓓 (F-interp-ob-comm B) (F-interp-ob-comm C)
    F-interp-ob-comm ⊤̬ = F .preserves-⊤
    -- hejohns: checked
    F-interp-ob-comm-inside-hom : {e : Q .edge} →
      𝓓 .cat [ F .functor ⟅ interpret-objects Q 𝓒 (ı .I-ob) (Q .dom e) ⟆ , F .functor ⟅ interpret-objects Q 𝓒 (ı .I-ob) (Q .cod e) ⟆ ] ≡ 𝓓 .cat [ interpret-objects Q 𝓓 (λ x → F .functor ⟅ ı .I-ob x ⟆) (Q .dom e) , interpret-objects Q 𝓓 (λ x → F .functor ⟅ ı .I-ob x ⟆) (Q .cod e) ]
    F-interp-ob-comm-inside-hom {e = e} = congS₂ (λ x y → 𝓓 .cat [ x , y ]) (F-interp-ob-comm (Q .dom e)) (F-interp-ob-comm (Q .cod e))
    -- extend interpretation along functor
    _∘I_ : Interp Q 𝓓
    _∘I_ .I-ob A = F .functor ⟅ ı .I-ob A ⟆
    _∘I_ .I-hom e =  transport F-interp-ob-comm-inside-hom (F .functor ⟪ ı .I-hom e ⟫) -- this transport causes so much pain
    -- by definition of _∘I_.I-hom
    F-interp-PathP : {e : Q .edge} → PathP (λ i → F-interp-ob-comm-inside-hom {e = e} i) (F .functor ⟪ ı .I-hom e ⟫) ((_∘I_) .I-hom e) 
    F-interp-PathP {e = e} = toPathP refl
  module _ {Q : ProductQuiver ℓq ℓq'}{𝓒 : BinaryCartesianCategory ℓc ℓc'}{𝓓 : BinaryCartesianCategory ℓd ℓd'}(F G : StrictCartesianFunctor 𝓒 𝓓)(ı : Interp Q 𝓒) where
    module _ (p : F ∘I ı ≡ G ∘I ı) where
      F-G-interp-Ihom-PathP-lem : {e : Q .edge}
        → 𝓓 .cat [ (interpret-objects Q 𝓓 ((F ∘I ı) .I-ob) (Q .dom e)) , (interpret-objects Q 𝓓 ((F ∘I ı) .I-ob) (Q .cod e)) ] ≡ 𝓓 .cat [ (interpret-objects Q 𝓓 ((G ∘I ı) .I-ob) (Q .dom e)) , (interpret-objects Q 𝓓 ((G ∘I ı) .I-ob) (Q .cod e)) ]
      F-G-interp-Ihom-PathP-lem {e = e} = congS (λ x → 𝓓 .cat [ (interpret-objects Q 𝓓 (x .I-ob) (Q .dom e)) , (interpret-objects Q 𝓓 (x .I-ob) (Q .cod e)) ]) p
      F-G-interp-Ihom-PathP : {e : Q .edge}
        → PathP (λ i → F-G-interp-Ihom-PathP-lem i) ((F ∘I ı) .I-hom e ) ((G ∘I ı) .I-hom e)
      F-G-interp-Ihom-PathP {e = e} = congP (λ i x → x .I-hom e) p
      F-G-Ihom-PathP-lem : {e : Q .edge}
        → 𝓓 .cat [ F .functor ⟅ interpret-objects Q 𝓒 (ı .I-ob) (Q .dom e) ⟆ , F .functor ⟅ interpret-objects Q 𝓒 (ı .I-ob) (Q .cod e) ⟆ ] ≡ 𝓓 .cat [ G .functor ⟅ interpret-objects Q 𝓒 (ı .I-ob) (Q .dom e) ⟆ , G .functor ⟅ interpret-objects Q 𝓒 (ı .I-ob) (Q .cod e) ⟆ ]
      F-G-Ihom-PathP-lem {e = e} = F-interp-ob-comm-inside-hom F ı ∙∙ F-G-interp-Ihom-PathP-lem ∙∙ sym (F-interp-ob-comm-inside-hom G ı)
      F-G-Ihom-PathP : {e : Q .edge}
        → PathP (λ i → F-G-Ihom-PathP-lem {e = e} i) (F .functor ⟪ ı .I-hom e ⟫) (G .functor ⟪ ı .I-hom e ⟫)
      F-G-Ihom-PathP {e = e} = F-interp-PathP F ı ⋆⋆ F-G-interp-Ihom-PathP ⋆⋆ symP (F-interp-PathP G ı)
open Data
open ProductQuiver
module _ (Q : ProductQuiver ℓq ℓq') where
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
  η : Interp Q FreeCartesianCategory
  η .I-ob = ↑̬
  η .I-hom e = transport⁻ inside-EdgeExpr (↑ₑ e)
    where
    inside-EdgeExpr : ∀{A B} → EdgeExpr[ interpret-objects Q FreeCartesianCategory ↑̬ A , interpret-objects Q FreeCartesianCategory ↑̬ B ] ≡ EdgeExpr[ A , B ]
    inside-EdgeExpr {A} {B} = congS₂ (λ x y → EdgeExpr[ x , y ]) (reinterp-trivial A) (reinterp-trivial B)
  module _ {𝓒 : BinaryCartesianCategory ℓc ℓc'}(F : StrictCartesianFunctor FreeCartesianCategory 𝓒) where
    --a : {e : Q .edge} → 𝓒 .cat [ F .functor ⟅ interpret-objects Q FreeCartesianCategory ↑̬ (Q .dom e) ⟆ , F .functor ⟅ interpret-objects Q FreeCartesianCategory ↑̬ (Q .cod e) ⟆ ]
    --a {e = e} = F .functor ⟪ η .I-hom e ⟫
    --b : {e : Q .edge} → 𝓒 .cat [ F .functor ⟅ Q .dom e ⟆ , F .functor ⟅ Q .cod e ⟆ ]
    --b {e = e} = F .functor ⟪ ↑ₑ e ⟫
    foobar : {e : Q .edge} → PathP (λ i → congS₂ (λ x y → 𝓒 .cat [ F .functor ⟅ x ⟆ , F .functor ⟅ y ⟆ ]) (reinterp-trivial (Q .dom e)) (reinterp-trivial (Q .cod e)) i) (F .functor ⟪ η .I-hom e ⟫) (F .functor ⟪ ↑ₑ e ⟫)
    foobar {e = e} = congP (λ i a → F .functor ⟪ a ⟫) (toPathP⁻ refl)
  module _ {𝓒 : BinaryCartesianCategory ℓc ℓc'}(F F' : StrictCartesianFunctor FreeCartesianCategory 𝓒) where
    module _ (agree-on-η : F ∘I η ≡ F' ∘I η) where
      open import Cubical.Foundations.HLevels
      open import Cubical.Foundations.Path
      open import Cubical.Foundations.Isomorphism
      open Iso
      aoo : ∀ t → F .functor ⟅ t ⟆ ≡ F' .functor ⟅ t ⟆
      aoo (↑̬ A) i = agree-on-η i .I-ob A
      aoo (A ×̬ B) = F .preserves-× ∙∙ inside-× 𝓒 (aoo A) (aoo B) ∙∙ sym (F' .preserves-×)
      -- F .preserves-× ∙ inside-× 𝓒 (aoo A) (aoo B) ∙ sym (F' .preserves-×)
      aoo ⊤̬ = F .preserves-⊤ ∙ sym (F' .preserves-⊤)
      aom-type : ∀{t t'} → (f : FreeCartesianCategory .cat [ t , t' ]) → Type _
      aom-type {t} {t'} f = PathP (λ i → congS₂ (λ x y → 𝓒 .cat [ x , y ]) (aoo t) (aoo t') i) (F .functor .F-hom f) (F' .functor .F-hom f)
      -- mnemonic
      F⟪-⟫≡F'⟪-⟫ = aom-type
      -- c/p Cubical.Categories.Constructions.Free.Category proof
      isProp-aom-type : ∀{t t'} → (f : FreeCartesianCategory .cat [ t , t' ]) → isProp (F⟪-⟫≡F'⟪-⟫ f)
      isProp-aom-type f = isPropRetract fromPathP toPathP (PathPIsoPath _ _ _ .leftInv) (𝓒 .cat .isSetHom _ _)
      aom : ∀{t t'} → (f : FreeCartesianCategory .cat [ t , t' ]) → F⟪-⟫≡F'⟪-⟫ f
      --aom = elimExpProp {P = F⟪-⟫≡F'⟪-⟫} isProp-aom-type (λ e → {!F-G-Ihom-PathP F F' η agree-on-η {e = e}!}) {!!} {!!} {!!} {!!} {!!} {!!}
      aom = elimExpProp {P = F⟪-⟫≡F'⟪-⟫} isProp-aom-type
        (λ e → toPathP (congS (λ x → {!!}) (fromPathP (symP (foobar F) ⋆⋆ F-G-Ihom-PathP {Q = Q} {𝓒 = FreeCartesianCategory} {𝓓 = 𝓒} F F' η agree-on-η {e = e} ⋆⋆ foobar F'))))
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
      ind = Functor≡ aoo aom
