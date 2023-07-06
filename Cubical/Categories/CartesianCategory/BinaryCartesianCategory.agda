{-# OPTIONS --safe #-}
module Cubical.Categories.CartesianCategory.BinaryCartesianCategory where
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open Category
private variable ℓ ℓ' : Level
record BinaryCartesianCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Category ℓ ℓ'
    _×_ : (A B : cat .ob) → cat .ob
    ⊤ : cat .ob
    π₁ : ∀{A B} → cat [ A × B , A ]
    π₂ : ∀{A B} → cat [ A × B , B ]
    ⟨_,_⟩ : ∀{A B C} → cat [ C , A ] → cat [ C , B ] → cat [ C , A × B ]
    ! : ∀{A} → cat [ A , ⊤ ]
    ×β₁ : ∀{A B C}{f : cat [ C , A ]}{g : cat [ C , B ]} → ⟨ f , g ⟩ ⋆⟨ cat ⟩ π₁ ≡ f
    ×β₂ : ∀{A B C}{f : cat [ C , A ]}{g : cat [ C , B ]} → ⟨ f , g ⟩ ⋆⟨ cat ⟩ π₂ ≡ g
    ×η : ∀{A B C}{f : cat [ C , A × B ]} → ⟨ f ⋆⟨ cat ⟩ π₁ , f ⋆⟨ cat ⟩ π₂ ⟩ ≡ f
    ⊤η : ∀{A}{f : cat [ A , ⊤ ] } → f ≡ !
