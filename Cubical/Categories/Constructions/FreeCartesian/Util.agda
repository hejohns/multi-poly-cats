{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.FreeCartesian.Util where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  A : Type ℓ
  B : Type ℓ'
  C : Type ℓ''
  D : Type ℓ'''
  a a' : A
  b b' : B
  c c' : C
  d : D
-- this has to be defined already somewhere... right?
congS₂ : (f : A → B → C)
  → a ≡ a'
  → b ≡ b'
  → f a b ≡ f a' b'
congS₂ f p q i = f (p i) (q i)
cong-transport-PathP : {eq₁ eq₂ : A ≡ B}
  → eq₂ ≡ eq₁
  → (p : PathP (λ i → eq₁ i) a b)
  → PathP (λ i → eq₂ i) a b
cong-transport-PathP {a = a} eq₁-₂ p = toPathP
  ((congS (λ x → transport x a) eq₁-₂) ∙ fromPathP p)
doubleCompP : {A B C D : Type ℓ} → ∀{a b c d}{eq₁ : A ≡ B}{eq₂ : B ≡ C}{eq₃ : C ≡ D}
  → (p : PathP (λ i → eq₁ i) a b)
  → (q : PathP (λ i → eq₂ i) b c)
  → (r : PathP (λ i → eq₃ i) c d)
  → PathP (λ i → (eq₁ ∙ eq₂ ∙ eq₃) i) a d
doubleCompP p q r = compPathP p (compPathP q r) -- this is the correct associativity
-- heterogeneous double composition, at the "proper" types
-- USAGE: eqₙ should be inferrable, but if you run into yellow, you can write it in manually
doubleCompP' : (eq₁ : A ≡ B)(eq₂ : B ≡ C)(eq₃ : C ≡ D)
  → (p : PathP (λ i → eq₁ i) a b)
  → (q : PathP (λ i → eq₂ i) b c)
  → (r : PathP (λ i → eq₃ i) c d)
  → PathP (λ i → (eq₁ ∙∙ eq₂ ∙∙ eq₃) i) a d
doubleCompP' {a = a} eq₁ eq₂ eq₃ p q r = cong-transport-PathP
  (doubleCompPath≡compPath eq₁ eq₂ eq₃)
  (doubleCompP p q r)
-- USAGE: implicit version of doubleCompP'
_⋆⋆_⋆⋆_ : {eq₁ : A ≡ B}{eq₂ : B ≡ C}{eq₃ : C ≡ D}
  → (p : PathP (λ i → eq₁ i) a b)
  → (q : PathP (λ i → eq₂ i) b c)
  → (r : PathP (λ i → eq₃ i) c d)
  → PathP (λ i → (eq₁ ∙∙ eq₂ ∙∙ eq₃) i) a d
_⋆⋆_⋆⋆_ {a = a} {eq₁ = eq₁} {eq₂ = eq₂} {eq₃ = eq₃} p q r = doubleCompP' eq₁ eq₂ eq₃ p q r
