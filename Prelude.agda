module Prelude where

data Unit : Set where
  unit : Unit
  
data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just  : a → Maybe a 

data ⊥ : Set where
    
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero  +N n = n
suc m +N n = suc (m +N n)
infixr 3 _+N_

record Σ {l} ( S : Set l) (T : S → Set l ) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public

data _+_ {l} (S : Set l) (T : Set l) : Set l where
  inl : S → S + T
  inr : T → S + T
  
record _*_  {l} (S : Set l) (T : Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T
open _*_ public
data _≡_ {l} {X : Set l} (x : X) :  X → Set l where
  refl : x ≡ x

infix 1 _≡_
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}



-- The category Set (without proof)
id  : {A : Set} → A → A
id x = x
_∘_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
(f ∘ g) x = g (f x) 
