{-# OPTIONS --copatterns #-}
module InteractionStructures where

open import Prelude

-- Subsets of S can be characterized by predicates:
--  { s ∈ S | P(s) }
-- We can encode this in agda as a function $ P : X → Set $.

-- This characterization of subsets gives rise to a functor
-- in the category Set:
Pow : (X : Set) → Set₁
Pow X = X → Set

-- If Pow gives us a predicate, then the functor over Pow is what we call a predicate transformer
-- and we can now show that Pow is indeed a functor in Set
-- Or:  any function on sets, can be turned into a function on predicates.
-- I.e.  what Peter Hancock calls a "Predicate Transformer"
Powₐ : { X Y : Set} → (f : X → Y) → (Pow Y → Pow X)
Powₐ f x y = x (f y)


-- the type of a witness that a predicate is always true, because it holds for each argument
-- of the predicate
[_] : {I : Set}(P : Pow I) → Set
[_] {I} P = {i : I} → P i



-- Pow  also gives rise to a category for each I, 
-- where the objects are indexed sets  A : Pow I
-- and the arrows are elements of  [ A -:> B ] for (A B : Pow I)
_-:>_ _×:_ _+:_ : {I : Set}(S T : Pow I) -> (Pow I) 

(S -:> T) i = S i -> T i   -- index-respecting functions
(S ×: T) i = S i × T i     -- index-matching pairs
(S +: T) i = S i + T i     -- index-consistent choice

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
record IxFunctor {I J : Set} (F : Pow I → Pow J) : Set1 where
  field
    mapIx : {X Y : Pow I} → [ X -:> Y ] → [ F X -:> F Y ]

-- what is a monad on Pow?
record IxMonad {W : Set} (F : Pow W → Pow W) : Set1 where
  field
    pure : {P : Pow W} → [ P -:> F P ]
    _=<<_ : {P Q : Pow W} → [ P -:> F Q ] → [ F P -:> F Q ]

  _>>=_ : ∀ {P Q w} → F P w → (∀ {v} → P v → F Q v) → F Q w
  fp >>= k = k =<< fp

record IxComonad {W : Set} (F : Pow W → Pow W) : Set₁ where
  coinductive
  field
    extract : {P : Pow W} → [ F P -:> P ]
    extend : { P Q : Pow W} → [ F P -:> Q ] → [ F P -:> F Q ]
  

-- every monad is trivially a  (endo)functor (without proof here)
monadIxFunctor : ∀ {W} {F} → IxMonad {W} F → IxFunctor {W} {W} F
monadIxFunctor M =
  record { mapIx = λ f → (_=<<_) (λ z → pure (f z))}
  where open IxMonad M
    

-- we now define Peter Hancock's interaction structure
-- Connor, whouldn't the arrow be the other way around?
record _▸_ (I J : Set) : Set₁ where
  field
    Cmd : Pow J
    Resp : (a : J) → ( b : Cmd a) → Set
    next : (a : J) → (b : Cmd a) →  (c : Resp a b) → I

-- We define two monotone predicate transformers:

-- A client:  I provide a command, and then I need to be
-- able to handle any kind of response to enter the next state
_○ : ∀ {I J} → (Φ : J ▸ I) → Pow J → Pow I
(Φ ○) P a =
  Σ (Cmd a)  (λ x → (y : Resp a x) → P (next a x y) )
  where open _▸_ Φ

-- A server : For any command that I receive, I should be able to
-- produce a response, and proceed to the next state.
_● : ∀ {I J} → (Φ : J ▸ I) → Pow J → Pow I
(Φ ●) P a =
  (x : Cmd a) → Σ (Resp a x) (λ y → P (next a x y))
  where open _▸_ Φ

-- when we take the free monad over ○ we can assign an interpretation to it.
-- because we can pattern match on the dependent pair, and learn the ocmmand,
-- and then decide on a proper interpretation.     

-- however the free monad over ● is problematic, as we cannot pattern match
-- on a function type. We can only produce functions.

-- however, a cofree comonad instance _would_ work!  in order to unfold a Cofree
-- Comonad, we need to provide a witness for a single step. i.e., construct a functor
-- inhabitant of ●. And this is possible because we can ceate functions.

-- Again in the analogy of servers and clients, Free ○ signifies a client. We can
-- receive commands and interpret them, and decide to stop at any time.

-- and the cofree comonad over ● naturally defines a server.  We have an infinite
-- rose tree  that defines for each state a function that if given a command,
-- decides to what subtree to go infinitely, always ready to answer questions.

--   foldCofree : (forall x. w x -> f x) -> w a -> Cofree f a
--    We could for exmaple fold it up to an endless rose tree, that has all possible
-- server interactions encoded.


--   foldFree : (forall x. f x -> m x) -> Free f x -> m a
-- we could

-- _○ forms a functor in Pow S
○-IxFunctor : {I J : Set} (S : I ▸ J) → IxFunctor (S ○)
○-IxFunctor S = record { mapIx = λ { f (s , k) → s , (λ p → f (k p))} } where open _▸_ S

-- _● forms a functor in Pow S
●-IxFunctor : {I J : Set} (S : I ▸ J) → IxFunctor (S ●)
●-IxFunctor {I} {J} S =
    record { mapIx = helper } 
    where
        open _▸_ S
        helper : {X Y : I → Set} →
                ({i : I} → X i → Y i) →
                {i : J} →
                ((x : Cmd i) → Σ (Resp i x) (λ y → X (next i x y))) →
                (x : Cmd i) → Σ (Resp i x) (λ y → Y (next i x y))
        helper f g x with g x
        helper f g x | fst₁ , snd₁ = fst₁ ,  f snd₁

-- a client corresponds to a Free IxMonad, and is given the
-- choice to provide a command, and then needs to handle any response
-- and then it can decide to terminate at any time
-- Corresponds to Hank's _>>○_ 
data Free○ {I : Set} (Φ : I ▸ I) (X : Pow I) (i : I) : Set where
  stop : (X -:> Free○ Φ X) i
  step : ((Φ ○) (Free○ Φ X) -:> Free○ Φ X) i

-- this has no interpretation As we can no pattern match on
--  (Φ ●) X, so we can not decide what M X to produce except
-- for "pure x" which is a very boring interpretation
-- hence we need to resort to a Cofree Comonad encoding,
-- at each step we need to produce an inhabitant of (Φ ●) X
data Free● {I : Set} (Φ : I ▸ I) (X : Pow I) (i : I) : Set where
  stop : (X -:> Free● Φ X) i
  step : ((Φ ●) (Free● Φ X) -:> Free● Φ X) i

{-  Note that we could have parameterized over the functor instead,
    yielding your  free monad definition that you are used to, however,
    we do not get Agda concvinced that this data type is strictly positive,
    hence we thread the ○ IxFunctor into the Free IxMonad directly.
data Free { I : Set } (F : Pow I → Pow I) (X : Pow I)  (i : I) : Set where
  stop : (X -:> Free F X) i
  step : ((F (Free F X)) -:> Free F X) i
-}

free○-IxMonad : {I : Set} (S : I ▸ I) → IxMonad (Free○ S)
free○-IxMonad S =
  record
  { pure = stop
  ; _=<<_ = graft
  }
  where
    graft : ∀ {I} {S : I ▸ I} {P Q : I → Set} →
        ({i : I} → P i → Free○ S Q i) → {i : I} → Free○ S P i → Free○ S Q i
    graft k (stop x) = k x
    graft k (step (s , f)) = step (s , (λ p → graft k (f p)))


-- a server corresponds to the Cofree IxComonad,  It's always alive,
-- and should be ready to choose a response of it's liking any time
-- that it gets any command
-- Corresponds to Hank's _>>●_
-- TODO I'm not sure yet if this is correct
record Cofree● {I : Set} (Φ : I ▸ I) (X : Pow I) (i : I) : Set where
  coinductive
  field
    alive : X i
    ready : ((Φ ●) (Cofree● Φ X) ) i

-- TODO show that the Cofree IxComonad is a IxComonad

-- TODO Show that given a Free Client and a Cofree Server, we can run a simulation

{-module  Lol where
    open IxComonad
    open Cofree●
    
    helper : ∀ {I} {S : I ▸ I} {P Q : I → Set} →
            ({i : I} → Cofree● S P i → Q i) →
            {i : I} → Cofree● S P i → Cofree● S Q i

    helper x x₁ = {!!}
    cofreeIxComonad :  {I : Set} (S : I ▸ I) → IxComonad (Cofree● S)
    extract (cofreeIxComonad S) = alive
    extend (cofreeIxComonad S) x x₁ with (x x₁) 
    ... | y =  {!!} -}
   {- 
        alive (helperExtract x)  = ?
        helperExtend : ∀ { P Q } →  [ Cofree● S P -:> Q ] → [ Cofree● S P -:> Cofree● S Q ]
        Cofree●.ready (helperExtend x y) with Cofree●.ready y
        ...| z = ? 
    -}


-- some stuff from Hank's thesis
abort : {S T : Set} → S ▸ T
abort =
  record
  { Cmd =  λ x → ⊥
  ; Resp = λ { a ()}
  ; next = λ { a () c}
  }


magic : {S T : Set} → S ▸ T
magic =
  record
  { Cmd =  λ x → Unit
  ; Resp =  λ a b →  ⊥
  ; next = λ a b → λ ()
  }

-- update the state determinisetically
update : { S  : Set} → (S → S) → S ▸ S
update f =
  record
  { Cmd = λ s → Unit
  ; Resp = λ a b → Unit
  ; next = λ a b c → f a
  }

-- note that abort = assert(False)
assert : {S : Set} (F : Pow S) → S ▸ S
assert F = 
  record
  { Cmd = F
  ; Resp =  λ a b → Unit
  ; next = λ a b c → a
  }

-- magic = assert(True)
assume : {S : Set} (F : Pow S) → S ▸ S
assume F =
  record
  { Cmd = λ x → Unit
  ; Resp = λ a b → F a
  ; next = λ a b c → a
  }

-- angelic choice (Given two possible states, choose which
-- one we want) (client)
_⊔_ : {S : Set} (Φ₁ : S ▸ S) (Φ₂ : S ▸ S) → S ▸ S
Φ₁ ⊔ Φ₂ =
  record
  { Cmd = (Cmd Φ₁) +: (Cmd Φ₂) 
  ; Resp = λ { k (inl x) → Resp Φ₁ k x
          ; k (inr x) → Resp Φ₂ k x
          }
  ; next = λ { k (inl x) r → next Φ₁ k x r
          ; k (inr x) r → next Φ₂ k x r
          }
  }
  where open _▸_
    
-- demonic choice we need to be able to respond to both
-- (server)
_⊓_ : {S : Set} (Φ₁ : S ▸ S) (Φ₂ : S ▸ S) → S ▸ S
Φ₁ ⊓ Φ₂ =
  record
  { Cmd =  Cmd Φ₁ ×: Cmd Φ₂
  ; Resp = λ { k (c1 , c2) →  Resp Φ₁ k c1 + Resp Φ₂ k c2 }
  ; next = λ { k (c1 , c2) (inl x) → next Φ₁ k c1 x 
          ; k (c1 , c2) (inr x) → next Φ₂ k c2 x
          } 
  }
  where open _▸_

-- add constant information J to the right hand side
growRight : {I J : Set } → I ▸ I → (I × J) ▸ (I × J)
growRight  x =
  record
  { Cmd = λ { (i , _) → Cmd x i }
  ; Resp = λ { (i , _) b → Resp x i b}
  ; next = λ { (i , j) b c → next x i b c , j }
  }
  where open _▸_

-- add constant information J to the left hand site 
growLeft : {I J : Set } → I ▸ I → (J × I) ▸ (J × I)
growLeft  x =
  record
  { Cmd = λ { (_ , i) → Cmd x i }
  ; Resp = λ { (_ , i) b → Resp x i b}
  ; next = λ { (j , i) b c → j , next x i b c }
  }
  where open _▸_

-- combine two interfaces that operate independently on separate
-- state.  Commands from one do not affect the other
_⊗_ : {I J : Set} → I ▸ I → J ▸ J → (I × J) ▸ (I × J)
_⊗_ {I} {J} ii jj = growLeft jj ⊔ growRight ii
  

--  Sequential composition flavors
-- note that we have folded these into the Free monad definitions. we do not need them
_>>○_ : ∀ {I J K} (Φ₁ : J ▸ I) → (Φ₂ : K ▸ J) → (K ▸ I)
_>>○_ Φ₁ Φ₂ =
  record
  { Cmd =  (Φ₁ ○) (Cmd Φ₂)
  ; Resp =  λ { a (b₁ , b₂) → Σ (Resp Φ₁ a b₁) (λ c₁ → Resp Φ₂ (next Φ₁ a b₁ c₁) (b₂ c₁)) }
  ; next =  λ { a (b₁ , b₂) (c₁ , c₂) → next Φ₂ (next Φ₁ a b₁ c₁) (b₂ c₁) c₂}
  }
  where open _▸_


_>>●_ : ∀ {I J K} (Φ₁ : J ▸ I) → (Φ₂ : K ▸ J) → (K ▸ I)
_>>●_ Φ₁ Φ₂ =
  record
    { Cmd = (Φ₁ ●) (Cmd Φ₂)
    ; Resp =  λ { s t → Σ (Cmd Φ₁ s) (λ c1 → Resp Φ₂ (next Φ₁ s c1 (fst (t c1))) (snd (t c1)))} 
    ; next = λ { s t (c1 , r2) → next Φ₂ (next Φ₁ s c1 (fst (t c1))) ( snd (t c1)) r2 }
    }

  where open _▸_

-- whatthefuck screams loudly, and then concludes everything is fine
whatthefuck : {A : Set} → ⊥ → A
whatthefuck ()

--- We continue to prove some interesting properties about interaction structures

-- Note. Agda will not normalize types by default, but when looking at holes
-- in hte case of using interaction structures, we do want normalization!

-- Type  C-u Cu C-c C-, for the normalized type 

-- if we try to serve a magic, the only choice is stopping immediately,
-- ortherwise we end up in a contradiction
magically● : Free● magic (λ _ → Unit) unit → Unit + ⊥
magically● (stop x) = inl x
magically● (step x) with x unit
magically● (step x) | contradiction , _ = inr  contradiction

-- when magic is consumed, we are given evidence of a contradiction, hence we
-- can conclude anything and continue. Hence magic can always be consumed
magically○ : Free○ magic (λ _ → Unit) unit
magically○  =  step (unit , (λ contradiction → whatthefuck contradiction))

-- an aborting computation must always stop immediatelly, any other action
-- is a contradiction
aborting○ : Free○ abort (λ _ → Unit) unit → Unit + ⊥
aborting○ (stop x) = inl x
aborting○ (step (contra , _)) = inr contra

-- abort can always be produced
aborting● : Free● abort (λ _ → Unit) unit
aborting● = step (λ contradiction → (whatthefuck contradiction) , stop unit)


-- what does this do exactly, nobody is sure
updating : {i : Nat} → Free○ (update (_+N_ 1)) (λ x → Nat) i
updating = step (unit , (λ { unit → stop 5}))
  where
    open IxMonad (free○-IxMonad (update (_+N_ 1)))




-- now to run a server we need a function:
-- given a natural transformation between the ○ functor and m
-- we are given a monad homomorphism from Free○ to m
--  foldFree (∀ {x} → (Φ ○) x i  → m x) → Free○ a i → m a

-- now to show that interaction structures compose

-- by interpreting Free○ HIGHLEVEL   as Free○ LOWLEVEL
-- by showing there is a natural transformation between the two
-- however, HIGHLEVEL, and LOWLEVEL are Interaction structures indexed over different state
-- so we need to do some more massaging 

●○ :
  {I J : Set}
  (Sync : I → J → Set)
  (Hi : I ▸ I)
  (Lo : J ▸ J)
  → Set

●○ {I} {J} Sync Hi Lo
  = ∀ i j
  → Sync i j         -- if states i and j are in sync
  → (c : Cmd Hi i)     -- and for all commands in the high level interface
  → Σ (Cmd Lo j) λ c'  -- there exists an equivalent in the low level interface
  → (r' : Resp Lo j c') -- and for all responses to that equivalent
  → Σ (Resp Hi i c) λ r -- we can find a response in the high level interface
  → Sync (next Hi i c r) (next Lo j c' r')  -- such that the states are _still_ in sync
  where
    open _▸_

  
drive :
  { I J : Set}
  {Sync : I → J → Set}
  {Hi : I ▸ I} {Lo : J ▸ J}
  (D : ●○ Sync Hi Lo)
  {X : Pow I}
  (i : I) (j : J)
  (ij : Sync i j) →
  (Hi ○) X i → (Lo ○) (λ j → Σ I λ i → Sync i j × X i) j

drive D i j ij (cmdₕ , condₕ) with D i j ij cmdₕ
drive {Hi = Hi} D i j ij (cmdₕ , condₕ) | cmdₗ , condₗ = cmdₗ ,  (λ y → next Hi i cmdₕ (fst (condₗ y)) , (snd (condₗ y) , condₕ (fst (condₗ y)))) 

  where open _▸_
  
{-
drive2 :
  { I J : Set}
  {Sync : I → J → Set}
  {Hi : I ▸ I} {Lo : J ▸ J}
  (D : ●○ Sync Hi Lo)
  {X : Pow I}
  (i : I) (j : J)
  (ij : Sync i j) →
  Free○  Hi X i →
  Free○ Lo (λ j → Σ I λ i → Sync i j × X i) j


drive2 D i j ij (stop x) = stop (i , (ij , x))
drive2 D i j ij (step (fst₁ , snd₁)) with D i j ij fst₁
drive2 D i j ij (step (fst₁ , snd₁)) | fst₂ , snd₂ = {!!}
  where open _▸_
-}
