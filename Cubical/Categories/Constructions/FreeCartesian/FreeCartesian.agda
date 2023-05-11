{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.FreeCartesian.FreeCartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Data.Graph.Base
private variable ℓ̬ ℓₑ : Level
private variable ℓₒ ℓₕ : Level
-- TODO: names tbd
open Cubical.Categories.Category.Base.Category
record CartesianCategory ℓₒ ℓₕ : Type (ℓ-suc (ℓ-max ℓₒ ℓₕ)) where
    field
        cat : Category ℓₒ ℓₕ
        _,,_ : (A B : ob cat) → ob cat -- binary product
        ⊤ : ob cat -- terminal object
        π₁ : {A B : ob cat} → cat [ A ,, B , A ] -- projections
        π₂ : {A B : ob cat} → cat [ A ,, B , B ]
        [_,,_] : {A B D : ob cat} → cat [ D , A ] → cat [ D , B ] → cat [ D , A ,, B ] -- pairing (ie existence of morphism into terminal cone)
        β₁ : {A B D : ob cat}{f : cat [ D , A ]}{g : cat [ D , B ]} → ([ f ,, g ] ⋆⟨ cat ⟩ π₁) ≡ f -- commuting conditions
        β₂ : {A B D : ob cat}{f : cat [ D , A ]}{g : cat [ D , B ]} → ([ f ,, g ]) ⋆⟨ cat ⟩ π₂ ≡ g
        ηₚ : {A B D : ob cat}{f : cat [ D , (A ,, B) ]} → [ (f ⋆⟨ cat ⟩ π₁) ,, (f ⋆⟨ cat ⟩ π₂) ] ≡ f -- ie uniqueness of morphism into terminal cone
        ! : {A : ob cat} → cat [ A , ⊤ ] -- existence
        η₁ : {A : ob cat}(f : cat [ A , ⊤ ]) → f ≡ ! -- uniqueness
open import Cubical.Categories.Functor.Base
open CartesianCategory hiding (η,⊤)
pairₒ : (𝓒 : CartesianCategory ℓₒ ℓₕ)(A B : ob (cat 𝓒)) → ob (cat 𝓒)
pairₒ = CartesianCategory._,,_
syntax pairₒ C A B = A ,,⟨ C ⟩ B
-- record CartesianFunctor ? where
--     field
--         functor : Functor 𝓒 𝓓
--         {𝓒 𝓓 : CartesianCategory ℓₒ ℓₕ}{F : Functor (cat 𝓒) (cat 𝓓)}(A B : ob (cat 𝓒)) → F ⟅ A ,,⟨ 𝓒 ⟩ B ⟆ ≡ (F ⟅ A ⟆ ,,⟨ 𝓓 ⟩ (F ⟅ B ⟆))
-- CartesianFunctor = {!!}
module _ (G : Graph ℓ̬ ℓₑ) where
    -- data of the FreeCartesianCategory
    data Objects : Type ℓ̬ where
        -- Category
        ↑_ : (A : Node G) → Objects -- include the generators
        isSetObjects : isSet Objects
        -- CartesianCategory
        _,_ : (A B : Objects) → Objects -- binary product
        symm : {A B : Objects} → (A , B) ≡ (B , A)
        assoc : {A B C : Objects} → (A , (B , C)) ≡ ((A , B) , C)
        ⊤ₒ : Objects -- freely throw in a terminal objcet
        idL : {A : Objects} → (⊤ₒ , A) ≡ A
    data Morphisms : Objects → Objects → Type (ℓ-max ℓ̬ ℓₑ) where
        -- Category
        ↑_ : {A B : Node G} → (f : Edge G A B) → Morphisms (↑ A) (↑ B)
        idₑ : {A : Objects} → Morphisms A A
        _⋆ₑ_ : {A B C : Objects} → Morphisms A B → Morphisms B C → Morphisms A C
        ⋆ₑIdL : {A B : Objects} (e : Morphisms A B) → idₑ ⋆ₑ e ≡ e
        ⋆ₑIdR : {A B : Objects} (e : Morphisms A B) → e ⋆ₑ idₑ ≡ e
        ⋆ₑAssoc : {A B C D : Objects} (e : Morphisms A B)(f : Morphisms B C)(g : Morphisms C D) → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
        isSetMorphisms : {A B : Objects} → isSet (Morphisms A B)
        -- CartesianCategory
        πₑ₁ : {A B : Objects} → Morphisms (A , B) A
        πₑ₂ : {A B : Objects} → Morphisms (A , B) B
        [_,_] : {A B D : Objects} → Morphisms D A → Morphisms D B → Morphisms D (A , B)
        βₑ₁ : {A B D : Objects}{f : Morphisms D A}{g : Morphisms D B} → ([ f , g ]) ⋆ₑ πₑ₁ ≡ f
        βₑ₂ : {A B D : Objects}{f : Morphisms D A}{g : Morphisms D B} → ([ f , g ]) ⋆ₑ πₑ₂ ≡ g
        ηₑ : {A B D : Objects}{f : Morphisms D (A , B)} → [ (f ⋆ₑ πₑ₁) , (f ⋆ₑ πₑ₂) ] ≡ f
        !ₑ : {A : Objects} → Morphisms A ⊤ₒ
        ηₑ₁ : {A : Objects}(f : Morphisms A ⊤ₒ) → f ≡ !ₑ
    FreeCartesianCat : CartesianCategory ℓ̬ (ℓ-max ℓ̬ ℓₑ)
    FreeCartesianCat = record
                         { cat = record
                            { ob = Objects
                            ; Hom[_,_] = Morphisms
                            ; id = idₑ
                            ; _⋆_ = _⋆ₑ_
                            ; ⋆IdL = ⋆ₑIdL
                            ; ⋆IdR = ⋆ₑIdR
                            ; ⋆Assoc = ⋆ₑAssoc
                            ; isSetHom = isSetMorphisms
                            }
                         ; _,,_ = _,_
                         ; ⊤ = ⊤ₒ
                         ; π₁ = πₑ₁
                         ; π₂ = πₑ₂
                         ; [_,,_] = [_,_]
                         ; β₁ = βₑ₁
                         ; β₂ = βₑ₂
                         ; ηₚ = ηₑ
                         ; ! = !ₑ
                         ; η₁ = ηₑ₁
                         }
    open import Cubical.Categories.Constructions.Free.UnderlyingGraph
    η : Interp G (cat FreeCartesianCat)
    η = record { _$g_ = λ x → ↑ x ; _<$g>_ = ↑_ }
    module Semantics (𝓒 : CartesianCategory ℓₒ ℓₕ)(𝑖 : GraphHom G (Ugr (cat 𝓒))) where
