
open import Category.Monad
open import Data.Empty
open import Function
open import Data.Unit
open import Data.Bool.Base using (Bool; true)
open import Data.Nat
open import Data.Sum using (inj₁; inj₂)
open import Data.Product renaming (_×_ to _⟨×⟩_)
open import Data.W
open import Level renaming (suc to sucl; zero to zerol)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------

module WithStdLib where

module NonIndexed where
  open import Data.Container
  open import Data.Container.Combinator
  open import Data.Container.FreeMonad

  data Cmd (S : Set) : Set where
    Get : Cmd S
    Put : S → Cmd S

  Resp : {S : Set} → Cmd S → Set
  Resp {S} Get = S
  Resp (Put x) = ⊤

  State : Set → Container _
  State S = Cmd S ▷ Resp


  get : ∀ {S} → State S ⋆ S
  get = do (Get , return)
    where
    open RawMonad rawMonad

  put : ∀ {S} → S → State S ⋆ ⊤
  put s = do (Put s , return)
    where
    open RawMonad rawMonad
  
  prog : State ℕ ⋆ Bool
  prog =
    get         >>= λ n →
    put (suc n) >>
    return true
    where
    open RawMonad rawMonad
  
  runState : ∀ {S X} → State S ⋆ X → (S → X ⟨×⟩ S)
  runState (sup (inj₁ x) f) s = x , s
  runState (sup (inj₂ Get) f) s = runState (f s) s
  runState (sup (inj₂ (Put s')) f) s = runState (f tt) s'
  
  test : runState prog 0 ≡ (true , 1)
  test = refl
  
  

module Indexed where
  open import Category.Monad.Predicate
  open import Data.W.Indexed
  open import Data.Container.Indexed
  open import Data.Container.Indexed.FreeMonad
  open import Relation.Unary hiding (U)

  data U : Set where
    ℕᵤ : U
    ⊤ᵤ : U

  el : U → Set
  el ℕᵤ = ℕ
  el ⊤ᵤ = ⊤


  data Cmd (S : U)  : Set where
    Get : Cmd S
    Put : {O : U} → el O → Cmd S


  Resp : {S : U} → Cmd S → Set
  Resp {S} Get = el S
  Resp (Put x) = ⊤


  next' : {o : U} (c : Cmd o) → Resp c → U
  next' {o} Get x = o
  next' (Put {O} x₁) x = O
  
  State :  Container U U _ _
  State = Cmd ◃ Resp / next'

  data AtKey {ℓ} {I : Set ℓ} ( X : Set ℓ) ( i : I) : I → Set ℓ where
    at : X → AtKey X i i

  get : ∀ {u} → (State ⋆ AtKey (el u) u) u
  get = do (Get , return? ∘ at)
    where open RawPMonad rawPMonad

  put :  {u₁ u₂ : U} → el u₂ → (State ⋆ AtKey ⊤ u₂) u₁
  put x = do (Put x , return? ∘ at)
    where open RawPMonad rawPMonad


  {-prog : State ℕ ⋆ Bool
  prog =
    get         >>= λ n →
    put (suc n) >>
    return true
    where
    open RawMonad rawMonad
  
  runState : ∀ {S X} → State S ⋆ X → (S → X ⟨×⟩ S)
  runState (sup (inj₁ x) f) s = x , s
  runState (sup (inj₂ Get) f) s = runState (f s) s
  runState (sup (inj₂ (Put s')) f) s = runState (f tt) s'
  
  test : runState prog 0 ≡ (true , 1)
  test = refl
-}
  
