{-# OPTIONS --safe #-}
module Cubical.Categories.CartesianCategory.BinaryCartesianCategory where
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open Category
private variable ℓ ℓ' : Level
record BinaryCartesianCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Category ℓ ℓ'
    _×_ : cat .ob → cat .ob → cat .ob
    ⊤ : cat .ob
    π₁ : ∀{A B} → cat [ A × B , A ]
    π₂ : ∀{A B} → cat [ A × B , B ]
    ⟨_,_⟩ : ∀{A B C} → cat [ C , A ] → cat [ C , B ] → cat [ C , A × B ]
    ! : ∀{A} → cat [ A , ⊤ ]
    ×β₁ : ∀{A B C}{f : cat [ C , A ]}{g : cat [ C , B ]} → ⟨ f , g ⟩ ⋆⟨ cat ⟩ π₁ ≡ f
    ×β₂ : ∀{A B C}{f : cat [ C , A ]}{g : cat [ C , B ]} → ⟨ f , g ⟩ ⋆⟨ cat ⟩ π₂ ≡ g
    ×η : ∀{A B C}{f : cat [ C , A × B ]} → ⟨ f ⋆⟨ cat ⟩ π₁ , f ⋆⟨ cat ⟩ π₂ ⟩ ≡ f
    ⊤η : ∀{A}{f : cat [ A , ⊤ ] } → f ≡ !
    -- TODO: I guess we need to require that cat has a set of objects?
    -- for equality of StrictCartesianFunctor s
    isSetOb : isSet (cat .ob)
open BinaryCartesianCategory
pair-objects : (C : BinaryCartesianCategory ℓ ℓ') → _ → _ → _
pair-objects A B = A × B
syntax pair-objects C A B = A ×⟨ C ⟩ B

private variable ℓc ℓc' ℓd ℓd' : Level
module _ (𝓒 : BinaryCartesianCategory ℓc ℓc')(𝓓 : BinaryCartesianCategory ℓd ℓd') where
  open import Cubical.Categories.Functor
  record StrictCartesianFunctor : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd')) where
    field
      functor : Functor (𝓒 .cat) (𝓓 .cat)
      respects-× : (∀{A B} → functor ⟅ A ×⟨ 𝓒 ⟩ B ⟆ ≡ functor ⟅ A ⟆ ×⟨ 𝓓 ⟩ functor ⟅ B ⟆)
      respects-⊤ : functor ⟅ 𝓒 .⊤ ⟆ ≡ 𝓓 .⊤
      --open import Cubical.HITs.PropositionalTruncation
      --respects-× : ∥ (∀{A B} → functor ⟅ A ×⟨ 𝓒 ⟩ B ⟆ ≡ functor ⟅ A ⟆ ×⟨ 𝓓 ⟩ functor ⟅ B ⟆) ∥₁
      --respects-⊤ : ∥ functor ⟅ 𝓒 .⊤ ⟆ ≡ 𝓓 .⊤ ∥₁
