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
open BinaryCartesianCategory
pair-objects : (C : BinaryCartesianCategory ℓ ℓ') → _ → _ → _
pair-objects A B = A × B
syntax pair-objects C A B = A ×⟨ C ⟩ B

private variable ℓ𝓒 ℓ𝓒' ℓ𝓓 ℓ𝓓' : Level
module _ (𝓒 : BinaryCartesianCategory ℓ𝓒 ℓ𝓒')(𝓓 : BinaryCartesianCategory ℓ𝓓 ℓ𝓓') where
  open import Cubical.Categories.Functor
  record StrictCartesianFunctor : Type (ℓ-max (ℓ-max ℓ𝓒 ℓ𝓒') (ℓ-max ℓ𝓓 ℓ𝓓')) where
    field
      functor : Functor (𝓒 .cat) (𝓓 .cat)
      respects-⊤ : functor ⟅ 𝓒 .⊤ ⟆ ≡ 𝓓 .⊤
      respects-× : ∀{A B} → functor ⟅ A ×⟨ 𝓒 ⟩ B ⟆ ≡ functor ⟅ A ⟆ ×⟨ 𝓓 ⟩ functor ⟅ B ⟆
