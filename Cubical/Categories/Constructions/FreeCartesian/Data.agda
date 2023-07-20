{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.FreeCartesian.Data where
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
open import Cubical.Categories.Constructions.FreeCartesian.Util
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
    -- shorten types w/ these aliases
    F⟅ı⟆ : (A : Q .vertex) → _
    F⟅ı⟆ A = F .functor ⟅ ı .I-ob A ⟆
    F⟪ı⟫ : (e : Q .edge) → _
    F⟪ı⟫ e = F .functor ⟪ ı .I-hom e ⟫
    F⟅interp⟆ : ∀ t → _
    F⟅interp⟆ t = F .functor ⟅ interpret-objects Q 𝓒 (ı .I-ob) t ⟆
    interpλF⟅ı⟆ : ∀ t → _
    interpλF⟅ı⟆ t = interpret-objects Q 𝓓 F⟅ı⟆ t
    F⟅interp⟆≡interpλF⟅ı⟆ : ∀ t → F⟅interp⟆ t ≡ interpλF⟅ı⟆ t
    F⟅interp⟆≡interpλF⟅ı⟆ (↑̬ B) = refl
    F⟅interp⟆≡interpλF⟅ı⟆ (B ×̬ C) = F .preserves-× ∙ inside-× 𝓓 (F⟅interp⟆≡interpλF⟅ı⟆ B) (F⟅interp⟆≡interpλF⟅ı⟆ C)
    F⟅interp⟆≡interpλF⟅ı⟆ ⊤̬ = F .preserves-⊤
    F⟅interp⟆≡interpλF⟅ı⟆-inside-hom : {e : Q .edge}
      → 𝓓 .cat [
        F⟅interp⟆ (Q .dom e) ,
        F⟅interp⟆ (Q .cod e) ]
      ≡ 𝓓 .cat [
        interpλF⟅ı⟆ (Q .dom e) ,
        interpλF⟅ı⟆ (Q .cod e) ]
    F⟅interp⟆≡interpλF⟅ı⟆-inside-hom {e = e} = congS (λ x → 𝓓 .cat [ x (Q .dom e) , x (Q .cod e) ]) (funExt F⟅interp⟆≡interpλF⟅ı⟆)
    -- extend interpretation along functor
    _∘I_ : Interp Q 𝓓
    _∘I_ .I-ob = F⟅ı⟆
    _∘I_ .I-hom e = transport F⟅interp⟆≡interpλF⟅ı⟆-inside-hom (F⟪ı⟫ e)
    F⟅interp⟆≡interpλF⟅ı⟆-inside-hom' : ((e : Q .edge)
        → 𝓓 .cat [
          F⟅interp⟆ (Q .dom e) ,
          F⟅interp⟆ (Q .cod e) ])
      ≡ ((e : Q .edge) → 𝓓 .cat [
          interpret-objects Q 𝓓 (_∘I_ .I-ob) (Q .dom e) ,
          interpret-objects Q 𝓓 (_∘I_ .I-ob) (Q .cod e) ])
    F⟅interp⟆≡interpλF⟅ı⟆-inside-hom' = congS (λ x → ((e : Q .edge) → 𝓓 .cat [ x (Q .dom e) , x (Q .cod e) ])) (funExt F⟅interp⟆≡interpλF⟅ı⟆)
    -- by definition of _∘I_ .I-hom
    F⟪ı⟫≡F∘Iı-Hom : (e : Q .edge) → PathP (λ i → F⟅interp⟆≡interpλF⟅ı⟆-inside-hom {e = e} i) (F⟪ı⟫ e) (_∘I_ .I-hom e)
    F⟪ı⟫≡F∘Iı-Hom e = toPathP refl
    F⟪ı⟫≡F∘Iı-Hom' : PathP (λ i → F⟅interp⟆≡interpλF⟅ı⟆-inside-hom' i) F⟪ı⟫ (_∘I_ .I-hom)
    F⟪ı⟫≡F∘Iı-Hom' = funExt F⟪ı⟫≡F∘Iı-Hom
  module _ {Q : ProductQuiver ℓq ℓq'}{𝓒 : BinaryCartesianCategory ℓc ℓc'}{𝓓 : BinaryCartesianCategory ℓd ℓd'}(F G : StrictCartesianFunctor 𝓒 𝓓)(ı : Interp Q 𝓒) where
    module _ (p : F ∘I ı ≡ G ∘I ı) where
      F∘Iı≡G∘Iı-Ob : (F ∘I ı) .I-ob ≡ (G ∘I ı) .I-ob
      F∘Iı≡G∘Iı-Ob = congS (λ x → x .I-ob) p
      F∘Iı≡G∘Iı-Hom-lem : ((e : Q .edge)
          → 𝓓 .cat [
            interpret-objects Q 𝓓 ((F ∘I ı) .I-ob) (Q .dom e) ,
            interpret-objects Q 𝓓 ((F ∘I ı) .I-ob) (Q .cod e) ])
        ≡ ((e : Q .edge)
          → 𝓓 .cat [
            interpret-objects Q 𝓓 ((G ∘I ı) .I-ob) (Q .dom e) ,
            interpret-objects Q 𝓓 ((G ∘I ı) .I-ob) (Q .cod e) ])
      F∘Iı≡G∘Iı-Hom-lem = congS
        (λ x → (e : Q .edge) → 𝓓 .cat [
            interpret-objects Q 𝓓 x (Q .dom e) ,
            interpret-objects Q 𝓓 x (Q .cod e) ])
        F∘Iı≡G∘Iı-Ob
      F∘Iı≡G∘Iı-Hom : PathP (λ i → F∘Iı≡G∘Iı-Hom-lem i)
          ((F ∘I ı) .I-hom)
          ((G ∘I ı) .I-hom)
      F∘Iı≡G∘Iı-Hom = congP (λ i x → x .I-hom) p
      F∘Iı≡G∘Iı-Hom' : (e : Q .edge) → _
      F∘Iı≡G∘Iı-Hom' e = congP (λ i x → x e) F∘Iı≡G∘Iı-Hom
      F⟪ı⟫≡G⟪ı⟫-Hom-lem : _
      F⟪ı⟫≡G⟪ı⟫-Hom-lem = F⟅interp⟆≡interpλF⟅ı⟆-inside-hom' F ı ∙∙ F∘Iı≡G∘Iı-Hom-lem ∙∙ sym (F⟅interp⟆≡interpλF⟅ı⟆-inside-hom' G ı)
      F⟪ı⟫≡G⟪ı⟫-Hom : PathP (λ i → F⟪ı⟫≡G⟪ı⟫-Hom-lem i) (F⟪ı⟫ F ı) (F⟪ı⟫ G ı)
      F⟪ı⟫≡G⟪ı⟫-Hom = F⟪ı⟫≡F∘Iı-Hom' F ı ⋆⋆ F∘Iı≡G∘Iı-Hom ⋆⋆ symP (F⟪ı⟫≡F∘Iı-Hom' G ı)
