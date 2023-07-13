{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where
open import Cubical.Foundations.Prelude
private variable ℓ ℓ' ℓ'' : Level
private variable ℓq ℓq' : Level
private variable ℓc ℓc' : Level
private variable ℓd ℓd' : Level
open import Cubical.Categories.Category
open Category
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
open BinaryCartesianCategory
open StrictCartesianFunctor
open import Cubical.Categories.Functor
module _ where -- helpers
  private variable
      A : Type ℓ
      B : Type ℓ'
      C : Type ℓ''
      a a' : A
      b b' : B
      c c' : C
  -- this has to be defined already somewhere... right?
  congS₂ : (f : A → B → C) → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  congS₂ f p q i = f (p i) (q i)
  --triple : {(a , b , c) (a' , b' , c') : Σ[ x ∈ A ] Σ[ b ∈ B ] C} → a ≡ a' → b ≡ b' → c ≡ c' → (a , b , c) ≡ (a' , b' , c')
  --triple p q r i = p i , q i  , r i
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
  inside-× : (𝓒 : BinaryCartesianCategory ℓc ℓc') → ∀{A A' B B'} → A ≡ A' → B ≡ B' → A ×⟨ 𝓒 ⟩ B ≡ A' ×⟨ 𝓒 ⟩ B'
  inside-× 𝓒 = congS₂ (λ x y → x ×⟨ 𝓒 ⟩ y)
  -- TODO: this is terrible
  interp-F-comm : (Q : ProductQuiver ℓq ℓq')(A : _)(𝓒 : BinaryCartesianCategory ℓc ℓc')(𝓓 : BinaryCartesianCategory ℓd ℓd')(F : StrictCartesianFunctor 𝓒 𝓓)(ı : Interp Q 𝓒) → interpret-objects Q 𝓓 (λ x → F .functor ⟅ (ı .I-ob x) ⟆) A ≡ F .functor ⟅ interpret-objects Q 𝓒 (ı .I-ob) A ⟆
  interp-F-comm Q (↑̬ B) 𝓒 𝓓 F ı = refl
  --interp-F-comm Q (B ×̬ C) 𝓒 𝓓 F ı = sym (F .respects-× ∙ congS (λ x → x ×⟨ 𝓓 ⟩ _) (sym (interp-F-comm Q B 𝓒 𝓓 F ı)) ∙ congS (λ x → _ ×⟨ 𝓓 ⟩ x) (sym (interp-F-comm Q C 𝓒 𝓓 F ı)))
  interp-F-comm Q (B ×̬ C) 𝓒 𝓓 F ı = sym (F .preserves-× ∙ inside-× 𝓓 (sym (interp-F-comm Q B 𝓒 𝓓 F ı)) (sym (interp-F-comm Q C 𝓒 𝓓 F ı)))
  interp-F-comm Q ⊤̬ 𝓒 𝓓 F ı = sym (F .preserves-⊤)
  _∘I_ : {Q : ProductQuiver ℓq ℓq'}{𝓒 : BinaryCartesianCategory ℓc ℓc'}{𝓓 : BinaryCartesianCategory ℓd ℓd'}(F : StrictCartesianFunctor 𝓒 𝓓)(ı : Interp Q 𝓒) → Interp Q 𝓓
  (F ∘I ı) .I-ob A = F .functor ⟅ ı .I-ob A ⟆
  --(F ∘I ı) .I-hom e = {!F .functor ⟪ ı .I-hom e ⟫!}
  (_∘I_ {Q = Q} {𝓒 = 𝓒} {𝓓 = 𝓓} F ı) .I-hom e =  transport (congS₂ (λ x y → 𝓓 .cat [ x , y ]) (sym (interp-F-comm Q (Q .dom e) 𝓒 𝓓 F ı)) (sym (interp-F-comm Q (Q .cod e) 𝓒 𝓓 F ı))) (F .functor ⟪ ı .I-hom e ⟫) 
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
  ×η-lemma : ∀{A B C f g} → (h : EdgeExpr[ C , A ×̬ B ]) → h ⋆ₑ π₁ₑ ≡ f → h ⋆ₑ π₂ₑ ≡ g → h ≡ ⟨ f ,ₑ g ⟩
  ×η-lemma h p q = (sym ×̬η) ∙ congS₂ (λ x y → ⟨ x ,ₑ y ⟩) p q
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
  FreeCartesianCategory .⊤ = ⊤̬
  FreeCartesianCategory .! = !ₑ
  FreeCartesianCategory .⊤η = ⊤̬η
  open Interp
  reinterp-trivial : (A : ProdTypeExpr') → interpret-objects Q FreeCartesianCategory ↑̬ A ≡ A
  reinterp-trivial (↑̬ B) = refl
  reinterp-trivial (B ×̬ C) i = reinterp-trivial B i ×̬ reinterp-trivial C i
  reinterp-trivial ⊤̬  = refl
  inside-EdgeExpr : ∀{A B} → EdgeExpr[ interpret-objects Q FreeCartesianCategory ↑̬ A , interpret-objects Q FreeCartesianCategory ↑̬ B ] ≡ EdgeExpr[ A , B ]
  inside-EdgeExpr {A} {B} = congS₂ (λ x y → EdgeExpr[ x , y ]) (reinterp-trivial A) (reinterp-trivial B)
  η : Interp Q FreeCartesianCategory
  η .I-ob = ↑̬
  η .I-hom e = transport (sym inside-EdgeExpr) (↑ₑ e)
  -- EdgeExpr[ (Q .dom e) , (Q .cod e) ]
  -- ≡
  -- EdgeExpr[
  --       (Q .dom e) ,
  --       interpret-objects Q FreeCartesianCategory ↑̬ (Q .cod e) ]
  -- ≡
  -- EdgeExpr[
  --       interpret-objects Q FreeCartesianCategory ↑̬ (Q .dom e) ,
  --       interpret-objects Q FreeCartesianCategory ↑̬ (Q .cod e) ]
  module _ {𝓒 : BinaryCartesianCategory ℓc ℓc'}(F F' : StrictCartesianFunctor FreeCartesianCategory 𝓒) where
    module _ (agree-on-η : F ∘I η ≡ F' ∘I η) where
      aoo : ∀ c → F .functor ⟅ c ⟆ ≡ F' .functor ⟅ c ⟆
      aoo (↑̬ A) i = agree-on-η i .I-ob A
      aoo (A ×̬ B) = F .preserves-× ∙ inside-× 𝓒 (aoo A) (aoo B) ∙ sym (F' .preserves-×)
      aoo ⊤̬ = F .preserves-⊤ ∙ sym (F' .preserves-⊤)
      ind' : F .functor ≡ F' .functor
      ind' = Functor≡ aoo {!!}
      ind : F ≡ F'
      ind i .functor = ind' i
      ind i .preserves-× = {!!}
      --ind i .preserves-⊤ = isProp→PathP (λ j → 𝓒 .isSetOb (ind' j ⟅ ⊤̬ ⟆) (𝓒 .⊤)) (F .respects-⊤) (F' .respects-⊤) i
