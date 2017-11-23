open import Prelude
open import InteractionStructures





R : {S : Set} → S → Pow S
R {S} = λ s s' → S
