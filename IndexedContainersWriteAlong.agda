
open import Data.Product as Prod hiding (map)
open import Level


infix 5 _▷_

record Container (ℓ : Level) : Set (suc ℓ) where
  constructor _▷_
  field
    Shape    : Set ℓ
    Position : Shape → Set ℓ

open Container public

-- The semantics ("extension") of a container.

⟦_⟧C : ∀ {ℓ₁ ℓ₂} → Container ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
-- Σ[ s ∈ Shape C ] (Position C s → X)
⟦ C ⟧C X = Σ (Shape C) λ x → Position C x → X 


record IndexedContainer (ℓ : Level) (I : Set ℓ) (O : Set ℓ) : Set (suc ℓ) where
  constructor Mk
  field
    Command : I → Set



