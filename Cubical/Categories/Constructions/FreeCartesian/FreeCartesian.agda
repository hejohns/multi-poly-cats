{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Data.Graph.Base

private variable ℓ̬ ℓₑ : Level

module _ (G : Graph ℓ̬ ℓₑ) where
    open Cubical.Categories.Category.Base.Category
    data Objects : Type ℓ̬ where
        ↑_ : (A : Node G) → Objects
        _,_ : (A B : Objects) → Objects
        symm : {A B : Objects} → (A , B) ≡ (B , A)
        assoc : {A B C : Objects} → (A , (B , C)) ≡ ((A , B) , C)
        ⊤ : Objects
        idL : {A : Objects} → (⊤ , A) ≡ A
        isSetObjects : isSet Objects
    open Objects
    data Morphisms : Objects → Objects → Type (ℓ-max ℓ̬ ℓₑ) where
        ↑_ : {A B : Node G} → (f : Edge G A B) → Morphisms (↑ A) (↑ B)
        idₑ : {A : Objects} → Morphisms A A
        _⋆ₑ_ : {A B C : Objects} → Morphisms A B → Morphisms B C → Morphisms A C
        ⋆ₑIdL : {A B : Objects} (e : Morphisms A B) → idₑ ⋆ₑ e ≡ e
        ⋆ₑIdR : {A B : Objects} (e : Morphisms A B) → e ⋆ₑ idₑ ≡ e
        ⋆ₑAssoc : {A B C D : Objects} (e : Morphisms A B)(f : Morphisms B C)(g : Morphisms C D)
                → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
        isSetMorphisms : {A B : Objects} → isSet (Morphisms A B)
        π₁ : {A B : Objects} → Morphisms (A , B) A
        π₂ : {A B : Objects} → Morphisms (A , B) B
        [_,_] : {A B D : Objects} → Morphisms D A → Morphisms D B → Morphisms D (A , B)
        β₁ : {A B D : Objects}{f : Morphisms D A}{g : Morphisms D B} → ([ f , g ]) ⋆ₑ π₁ ≡ f
        β₂ : {A B D : Objects}{f : Morphisms D A}{g : Morphisms D B} → ([ f , g ]) ⋆ₑ π₂ ≡ g
        η : {A B D : Objects}{f : Morphisms D (A , B)} → [ (f ⋆ₑ π₁) , (f ⋆ₑ π₂) ] ≡ f

    FreeCartesianCat : Category ℓ̬ (ℓ-max ℓ̬ ℓₑ)
    FreeCartesianCat = record
                        { ob = Objects
                        ; Hom[_,_] = Morphisms
                        ; id = idₑ
                        ; _⋆_ = _⋆ₑ_
                        ; ⋆IdL = ⋆ₑIdL
                        ; ⋆IdR = ⋆ₑIdR
                        ; ⋆Assoc = ⋆ₑAssoc
                        ; isSetHom = isSetMorphisms
                        }
