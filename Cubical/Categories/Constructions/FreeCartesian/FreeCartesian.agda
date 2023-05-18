{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Data.Graph.Base
private variable ℓ̬ ℓₑ : Level -- (graph) vertice and edge levels
private variable ℓₒ ℓₕ : Level -- (category) object and hom levels)
module Construction (G : Graph ℓ̬ ℓₑ) where
    open import Cubical.Data.FinSet.Base
    open import Cubical.Foundations.Structure
    data FreeCartesianCategory₀ : Type (ℓ-suc (ℓ-max ℓ̬ ℓₑ)) where -- objects
        ↑_ : Node G → FreeCartesianCategory₀ -- inclusion of generators
        Π : (J : FinSet ℓ-zero) → (⟨ J ⟩ → FreeCartesianCategory₀) → FreeCartesianCategory₀ -- see TypeWithStr for ⟨_⟩
    data FreeCartesianCategory₁ : FreeCartesianCategory₀ → FreeCartesianCategory₀ → Type (ℓ-suc (ℓ-max ℓ̬ ℓₑ)) where -- morphisms
        -- Category
        ↑_ : {A B : Node G}(f : Edge G A B) → FreeCartesianCategory₁ (↑ A) (↑ B) -- inclusion of generators
        id : {A : FreeCartesianCategory₀} → FreeCartesianCategory₁ A A
        _⋆_ : {A B C : FreeCartesianCategory₀} → FreeCartesianCategory₁ A B → FreeCartesianCategory₁ B C → FreeCartesianCategory₁ A C -- diagrammatic order composition
        ⋆IdL : {A B : FreeCartesianCategory₀} (f : FreeCartesianCategory₁ A B) → id ⋆ f ≡ f
        ⋆IdR : {A B : FreeCartesianCategory₀} (f : FreeCartesianCategory₁ A B) → f ⋆ id ≡ f
        ⋆Assoc : {A B C D : FreeCartesianCategory₀} (f : FreeCartesianCategory₁ A B)(g : FreeCartesianCategory₁ B C)(h : FreeCartesianCategory₁ C D) → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
        isSetHom : {A B : FreeCartesianCategory₀} → isSet (FreeCartesianCategory₁ A B) -- TODO: why do we need this?
        -- CartesianCategory
        -- TODO: how do you module this so it isn't terrible
        π : {J : FinSet ℓ-zero}{obs : ⟨ J ⟩ → FreeCartesianCategory₀} → (j : ⟨ J ⟩) → FreeCartesianCategory₁ (Π J obs) (obs j) 
        -- why is this called prod-I ?
        prod-I : {J : FinSet ℓ-zero}{obs : ⟨ J ⟩ → FreeCartesianCategory₀}{D : FreeCartesianCategory₀} → (fs : (j : ⟨ J ⟩) → FreeCartesianCategory₁ D (obs j)) → FreeCartesianCategory₁ D (Π J obs)
        β : {J : FinSet ℓ-zero}{obs : ⟨ J ⟩ → FreeCartesianCategory₀}{D : FreeCartesianCategory₀} → (fs : (j : ⟨ J ⟩) → FreeCartesianCategory₁ D (obs j)) → (j : ⟨ J ⟩) → (prod-I {J} fs) ⋆ π j ≡  fs j
        η : {J : FinSet ℓ-zero}{obs : ⟨ J ⟩ → FreeCartesianCategory₀}{D : FreeCartesianCategory₀}{f : FreeCartesianCategory₁ D (Π J obs)} → prod-I (λ j → f ⋆ (π j)) ≡ f
    open import UMP
    open import Cubical.Categories.Presheaf.Representable
    FreeCartesianCategory : CartesianCategory (ℓ-suc (ℓ-max ℓ̬ ℓₑ)) (ℓ-suc (ℓ-max ℓ̬ ℓₑ))
    FreeCartesianCategory = record { cat = cat
                              ; finite-products = λ J' obs → record { vertex = Π J' obs ; element = π ; universal = record { coinduction = prod-I ; commutes = λ ϕ i j → β {J'} ϕ j i ; is-uniq = λ ϕ f x → f ≡⟨ sym η ⟩ prod-I (λ j → f ⋆ (π j)) ≡⟨ (λ i → prod-I (x i)) ⟩ prod-I ϕ ∎} } }
        where
        cat : Category (ℓ-suc (ℓ-max ℓ̬ ℓₑ)) (ℓ-suc (ℓ-max ℓ̬ ℓₑ))
        cat = record { ob = FreeCartesianCategory₀
                     ; Hom[_,_] = FreeCartesianCategory₁
                     ; id = FreeCartesianCategory₁.id
                     ; _⋆_ = FreeCartesianCategory₁._⋆_
                     ; ⋆IdL = FreeCartesianCategory₁.⋆IdL
                     ; ⋆IdR = FreeCartesianCategory₁.⋆IdR
                     ; ⋆Assoc = FreeCartesianCategory₁.⋆Assoc
                     ; isSetHom = FreeCartesianCategory₁.isSetHom
                     }
    open import Cubical.Categories.RezkCompletion
    open Cubical.Categories.RezkCompletion.RezkByYoneda
    open import Cubical.Categories.Functor.Base
    UnivalentFreeCartesianCategory : CartesianCategory (ℓ-suc (ℓ-suc (ℓ-max ℓ̬ ℓₑ))) (ℓ-suc (ℓ-max ℓ̬ ℓₑ))
    UnivalentFreeCartesianCategory = record { cat = YonedaImage (CartesianCategory.cat FreeCartesianCategory) ; finite-products = λ J' obs → record { vertex = {!ToYonedaImage ⟅ Π J' obs ⟆!} ; element = {!!} ; universal = {!!} } }
    -- YonedaImage (CartesianCategory.cat FreeCartesianCategory)
module Semantics (G : Graph ℓ̬ ℓₑ) where
    open import Cubical.Categories.Constructions.Free.UnderlyingGraph
    open import UMP
    open Construction hiding (η)
    η : Interp G (CartesianCategory.cat (FreeCartesianCategory G))
    η = record { _$g_ = λ x → ↑ x
               ; _<$g>_ = ↑_
               }
    module Properties (𝓒 : CartesianCategory ℓₒ ℓₕ)(𝑖 : GraphHom G (Ugr (CartesianCategory.cat 𝓒))) where
