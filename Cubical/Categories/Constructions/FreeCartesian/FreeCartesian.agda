{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Data.Graph.Base
private variable ℓ̬ ℓₑ : Level -- (graph) vertice and edge levels
private variable ℓₒ ℓₕ : Level -- (category) object and hom levels)
module _ (G : Graph ℓ̬ ℓₑ) where
    open import Cubical.Data.FinSet.Base
    open import Cubical.Foundations.Structure
    data FreeCartesianCategory₀ : Type (ℓ-suc ℓ̬) where -- objects
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
    FreeCartesianCat : CartesianCategory (ℓ-suc ℓ̬) (ℓ-suc (ℓ-max ℓ̬ ℓₑ))
    FreeCartesianCat = record { cat = cat
                              ; finite-products = λ J' obs → record { vertex = Π J' obs ; element = π ; universal = record { coinduction = prod-I ; commutes = λ ϕ i j → β {J'} ϕ j i ; is-uniq = λ ϕ f x → f ≡⟨ sym η ⟩ prod-I (λ j → f ⋆ (π j)) ≡⟨ (λ i → prod-I (x i)) ⟩ prod-I ϕ ∎} } }
        where
        cat : Category (ℓ-suc ℓ̬) (ℓ-suc (ℓ-max ℓ̬ ℓₑ))
        cat = record { ob = FreeCartesianCategory₀
                     ; Hom[_,_] = FreeCartesianCategory₁
                     ; id = FreeCartesianCategory₁.id
                     ; _⋆_ = FreeCartesianCategory₁._⋆_
                     ; ⋆IdL = FreeCartesianCategory₁.⋆IdL
                     ; ⋆IdR = FreeCartesianCategory₁.⋆IdR
                     ; ⋆Assoc = FreeCartesianCategory₁.⋆Assoc
                     ; isSetHom = FreeCartesianCategory₁.isSetHom
                     }
--     FreeCartesianCat : CartesianCategory ℓ̬ (ℓ-max ℓ̬ ℓₑ)
--     FreeCartesianCat = record
--                          { cat = record
--                             { ob = Objects
--                             ; Hom[_,_] = Morphisms
--                             ; id = idₑ
--                             ; _⋆_ = _⋆ₑ_
--                             ; ⋆IdL = ⋆ₑIdL
--                             ; ⋆IdR = ⋆ₑIdR
--                             ; ⋆Assoc = ⋆ₑAssoc
--                             ; isSetHom = isSetMorphisms
--                             }
--                          ; _,,_ = _,_
--                          ; ⊤ = ⊤ₒ
--                          ; π₁ = πₑ₁
--                          ; π₂ = πₑ₂
--                          ; [_,,_] = [_,_]
--                          ; β₁ = βₑ₁
--                          ; β₂ = βₑ₂
--                          ; ηₚ = ηₑ
--                          ; ! = !ₑ
--                          ; η₁ = ηₑ₁
--                          }
--     open import Cubical.Categories.Constructions.Free.UnderlyingGraph
--     η : Interp G (cat FreeCartesianCat)
--     η = record { _$g_ = λ x → ↑ x ; _<$g>_ = ↑_ }
--     module Semantics (𝓒 : CartesianCategory ℓₒ ℓₕ)(𝑖 : GraphHom G (Ugr (cat 𝓒))) where
