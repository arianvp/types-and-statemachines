data _≡_ {l} {X : Set l} (x : X) :  X → Set l where
  refl : x ≡ x

infix 1 _≡_
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

-- Subsets of S can be characterized by predicates:
--  { s ∈ S | P(s) }
-- We can encode this in agda as a function $ P : X → Set $.

-- This characterization of subsets gives rise to a functor
-- in the category Set:


-- The category Set (without proof)
id  : {A : Set} → A → A
id x = x
_∘_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
(f ∘ g) x = g (f x) 

Pow : (X : Set) → Set₁
Pow X = X → Set

-- and we can now show that Pow is indeed a functor in Set
-- Or:  any function on sets, can be turned into a function on predicates.
-- I.e.  what Peter Hancock calls a "Predicate Transformer"
Powₐ : { X Y : Set} → (f : X → Y) → (Pow Y → Pow X)
Powₐ f x y = x (f y)


-- the type of a witness that a predicate is always true:
[_] : {I : Set}(P : Pow I) → Set
[_] {I} P = {i : I} → P i


-- Pow  also gives rise to a category for each I, 
-- where the objects are indexed sets  A : Pow I
-- and the arrows are elements of  [ A -:> B ] for (A B : Pow I)
_-:>_ : {I : Set} (S : Pow I) → (T : Pow I) → Pow I
(S -:> T) i = S i → T i


-- Each object A can be assigned an identity morphism A → A
idₚ : {I : Set} {i : I} → (A : Pow I) → (A i → A i)
idₚ = λ A z → z

-- there is a composition of morphisms
compose
  : {I : Set} {A B C : Pow I} {i : I}
  → (A i → B i)
  → (B i → C i)
  → (A i → C i)
compose f g = λ x → g (f x)


-- and composition and id adhere to the category laws
lunit
  : {I : Set} {i : I } {A B  : Pow I}
  → (f : A i → B i)
  → (compose {A = A} {B = B} {B} f (idₚ B)  ≡ f)
lunit f = refl

runit
  : {I : Set} {i : I } {A B  : Pow I}
  → (f : A i → B i)
  → (compose {A = A} {B = A} {C = B}  (idₚ A) f ≡ f)
runit f = refl

compose-assoc
  : { I : Set} { A B C D : Pow I} {i : I}
  → (f : A i → B i)
  → (g : B i → C i)
  → (h : C i → D i)
  → compose {A = A} {B = B} {C = D} f (compose {A = B} {B = C} {C = D} g h)
  ≡ compose {A = A} {B = C} {C = D}   (compose {A = A} {B = B} {C = C} f g) h
compose-assoc f g h = refl
  

  
-- We define what is a functor between two categories Pow I and Pow J
record Functor {I J : Set} (F : Pow I → Pow J) : Set1 where
  field
    mapIx : {A B : Pow I} → [ A -:> B ] → [ F A -:> F B ]

-- what is a monad on Pow?
record Monad {W : Set} (F : Pow W → Pow W) : Set1 where
  field
    pure : {P : Pow W} → [ P -:> F P ]
    _=<<_ : {P Q : Pow W} → [ P -:> F Q ] → [ F P -:> F Q ]

  _>>=_ : ∀ {P Q w} → F P w → (∀ {v} → P v → F Q v) → F Q w
  fp >>= k = k =<< fp

-- every monad is trivially a  (endo)functor (without proof here)
monadFunctor : ∀ {W} {F} → Monad {W} F → Functor {W} {W} F
monadFunctor M =
  record { mapIx = λ f → (_=<<_) (λ z → pure (f z))}
  where open Monad M
    
    
record Σ {l} ( S : Set l) (T : S → Set l ) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public

-- we now define Peter Hancock's interaction structure
-- Connor, whouldn't the arrow be the other way around?
record _⇒_ (I J : Set) : Set₁ where
  field
    B : Pow J
    C : (a : J) → ( b : B a) → Set
    d : (a : J) → (b : B a) →  (c : C a b) → I

-- We define two predicate transformers:
-- there exists a command, such that for all responses
_○ : ∀ {I J} → (Φ : J ⇒ I) → Pow J → Pow I
(Φ ○) P a =
  Σ (B a)  (λ x → (y : C a x) → P (d a x y) )
  where open _⇒_ Φ

-- for all commands, there exists a response
_● : ∀ {I J} → (Φ : J ⇒ I) → Pow J → Pow I
(Φ ●) P a =
  (x : B a) → Σ (C a x) (λ y → P (d a x y))
  where open _⇒_ Φ


-- a[b/c] = d(a,b,c)
_>>○_ : ∀ {I J K} (Φ₁ : J ⇒ I) → (Φ₂ : K ⇒ J) → (K ⇒ I)
_>>○_ Φ₁ Φ₂ =
  record
  { B =  (Φ₁ ○) (B Φ₂)
  ; C =  λ { a (b₁ , b₂) → Σ (C Φ₁ a b₁) (λ c₁ → C Φ₂ (d Φ₁ a b₁ c₁) (b₂ c₁)) }
  ; d =  λ { a (b₁ , b₂) (c₁ , c₂) → d Φ₂ (d Φ₁ a b₁ c₁) (b₂ c₁) c₂}
  }
  where open _⇒_

module Lol where
  open _⇒_

  _>>●_ : ∀ {I J K} (Φ₁ : J ⇒ I) → (Φ₂ : K ⇒ J) → (K ⇒ I)
  _>>●_ Φ₁ Φ₂ =
    record
      { B = (Φ₁ ●) (B Φ₂)
      ; C =  {! !}
      ; d = {!!}
      }

open Lol


-- interaction structures form a functor
IS : { I J : Set} → I ⇒ J → (Pow I → Pow J)
IS {I} {J} S X j = Σ (B j) (λ s → (p : C j s) → X (d j s p ))
  where open _⇒_ S

isFunctor : {I J : Set} (S : I ⇒ J) → Functor (IS S)
isFunctor S = record { mapIx = λ { f (s , k) → s , (λ p → f (k p))} } where open _⇒_ S


-- we now define the Free Monad du jour

data Free {I : Set} (S : I ⇒ I) (X : Pow I) (i : I) : Set where
  pure : (X -:> Free S X) i
  step : (IS S (Free S X) -:> Free S X) i
  

freeMonad : {I : Set} (S : I ⇒ I) → Monad (Free S)
freeMonad S =
  record
  { pure = pure
  ; _=<<_ = graft
  }
  where
    graft : ∀ {I} {S : I ⇒ I} {P Q : I → Set} →
        ({i : I} → P i → Free S Q i) → {i : I} → Free S P i → Free S Q i
    graft k (pure x) = k x
    graft k (step (s , f)) = step (s , (λ p → graft k (f p)))



data State : Set where
  Opened Closed : State

data  Command : State → Set where
  Open : Command Closed
  Close Read : Command Opened


is : State ⇒ State
is = {!!}

