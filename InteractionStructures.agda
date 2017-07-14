{-# OPTIONS --copatterns #-}
module InteractionStructures where
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
_-:>_ _*:_ _+:_ : {I : Set}(S T : Pow I) -> (Pow I) 

(S -:> T) i = S i -> T i   -- index-respecting functions
(S *: T) i = S i * T i     -- index-matching pairs
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
record Functor {I J : Set} (F : Pow I → Pow J) : Set1 where
  field
    mapIx : {X Y : Pow I} → [ X -:> Y ] → [ F X -:> F Y ]

-- what is a monad on Pow?
record Monad {W : Set} (F : Pow W → Pow W) : Set1 where
  field
    pure : {P : Pow W} → [ P -:> F P ]
    _=<<_ : {P Q : Pow W} → [ P -:> F Q ] → [ F P -:> F Q ]

  _>>=_ : ∀ {P Q w} → F P w → (∀ {v} → P v → F Q v) → F Q w
  fp >>= k = k =<< fp

record Comonad {W : Set} (F : Pow W → Pow W) : Set₁ where
  coinductive
  field
    extract : {P : Pow W} → [ F P -:> P ]
    extend : { P Q : Pow W} → [ F P -:> Q ] → [ F P -:> F Q ]
  

-- every monad is trivially a  (endo)functor (without proof here)
monadFunctor : ∀ {W} {F} → Monad {W} F → Functor {W} {W} F
monadFunctor M =
  record { mapIx = λ f → (_=<<_) (λ z → pure (f z))}
  where open Monad M
    

-- we now define Peter Hancock's interaction structure
-- Connor, whouldn't the arrow be the other way around?
record _▸_ (I J : Set) : Set₁ where
  field
    B : Pow J
    C : (a : J) → ( b : B a) → Set
    d : (a : J) → (b : B a) →  (c : C a b) → I

-- We define two monotone predicate transformers:

-- A client:  I provide a command, and then I need to be
-- able to handle any kind of response to enter the next state
_○ : ∀ {I J} → (Φ : J ▸ I) → Pow J → Pow I
(Φ ○) P a =
  Σ (B a)  (λ x → (y : C a x) → P (d a x y) )
  where open _▸_ Φ

-- A server : For any command that I receive, I should be able to
-- produce a response, and proceed to the next state.
_● : ∀ {I J} → (Φ : J ▸ I) → Pow J → Pow I
(Φ ●) P a =
  (x : B a) → Σ (C a x) (λ y → P (d a x y))
  where open _▸_ Φ



-- _○ forms a functor in Pow S
○-Functor : {I J : Set} (S : I ▸ J) → Functor (S ○)
○-Functor S = record { mapIx = λ { f (s , k) → s , (λ p → f (k p))} } where open _▸_ S

-- _● forms a functor in Pow S
--  C-u C-u <whatever>
●-Functor : {I J : Set} (S : I ▸ J) → Functor (S ●)
●-Functor {I} {J} S =
    record { mapIx = helper } 
    where
        open _▸_ S
        helper : {X Y : I → Set} →
                ({i : I} → X i → Y i) →
                {i : J} →
                ((x : B i) → Σ (C i x) (λ y → X (d i x y))) →
                (x : B i) → Σ (C i x) (λ y → Y (d i x y))
        helper f g x with g x
        helper f g x | fst₁ , snd₁ = fst₁ ,  f snd₁

-- a client corresponds to a Free Monad, and is given the
-- choice to provide a command, and then needs to handle any response
-- and then it can decide to terminate at any time
-- Corresponds to Hank's _>>○_ 
data Free○ {I : Set} (Φ : I ▸ I) (X : Pow I) (i : I) : Set where
  stop : (X -:> Free○ Φ X) i
  step : ((Φ ○) (Free○ Φ X) -:> Free○ Φ X) i

data Free● {I : Set} (Φ : I ▸ I) (X : Pow I) (i : I) : Set where
  stop : (X -:> Free● Φ X) i
  step : ((Φ ●) (Free● Φ X) -:> Free● Φ X) i

{-  Note that we could have parameterized over the functor instead,
    yielding your  free monad definition that you are used to, however,
    we do not get Agda concvinced that this data type is strictly positive,
    hence we thread the ○ Functor into the Free Monad directly.
data Free { I : Set } (F : Pow I → Pow I) (X : Pow I)  (i : I) : Set where
  stop : (X -:> Free F X) i
  step : ((F (Free F X)) -:> Free F X) i
-}

free○-Monad : {I : Set} (S : I ▸ I) → Monad (Free○ S)
free○-Monad S =
  record
  { pure = stop
  ; _=<<_ = graft
  }
  where
    graft : ∀ {I} {S : I ▸ I} {P Q : I → Set} →
        ({i : I} → P i → Free○ S Q i) → {i : I} → Free○ S P i → Free○ S Q i
    graft k (stop x) = k x
    graft k (step (s , f)) = step (s , (λ p → graft k (f p)))


-- a server corresponds to the Cofree Comonad,  It's always alive,
-- and should be ready to choose a response of it's liking any time
-- that it gets any command
-- Corresponds to Hank's _>>●_
-- TODO I'm not sure yet if this is correct
record Cofree● {I : Set} (Φ : I ▸ I) (X : Pow I) (i : I) : Set where
  coinductive
  field
    alive : X i
    ready : ((Φ ●) (Cofree● Φ X) ) i

-- TODO show that the Cofree Comonad is a Comonad

-- TODO Show that given a Free Client and a Cofree Server, we can run a simulation

module  Lol where
    open Comonad
    open Cofree●
    
    helper : ∀ {I} {S : I ▸ I} {P Q : I → Set} →
            ({i : I} → Cofree● S P i → Q i) →
            {i : I} → Cofree● S P i → Cofree● S Q i

    helper x x₁ = {!!}
    cofreeComonad :  {I : Set} (S : I ▸ I) → Comonad (Cofree● S)
    extract (cofreeComonad S) = alive
    extend (cofreeComonad S) =  helper
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
  { B =  λ x → ⊥
  ; C = λ { a ()}
  ; d = λ { a () c}
  }


magic : {S T : Set} → S ▸ T
magic =
  record
  { B =  λ x → Unit
  ; C =  λ a b →  ⊥
  ; d = λ a b → λ ()
  }

-- update the state determinisetically
update : { S  : Set} → (S → S) → S ▸ S
update f =
  record
  { B = λ s → Unit
  ; C = λ a b → Unit
  ; d = λ a b c → f a
  }

-- note that abort = assert(False)
assert : {S : Set} (F : Pow S) → S ▸ S
assert F = 
  record
  { B = F
  ; C =  λ a b → Unit
  ; d = λ a b c → a
  }

-- magic = assert(True)
assume : {S : Set} (F : Pow S) → S ▸ S
assume F =
  record
  { B = λ x → Unit
  ; C = λ a b → F a
  ; d = λ a b c → a
  }

-- angelic choice (Given two possible states, choose which
-- one we want) (client)
_⊔_ : {S : Set} (Φ₁ : S ▸ S) (Φ₂ : S ▸ S) → S ▸ S
Φ₁ ⊔ Φ₂ =
  record
  { B = (B Φ₁) +: (B Φ₂) 
  ; C = λ { k (inl x) → C Φ₁ k x
          ; k (inr x) → C Φ₂ k x
          }
  ; d = λ { k (inl x) r → d Φ₁ k x r
          ; k (inr x) r → d Φ₂ k x r
          }
  }
  where open _▸_
    
-- demonic choice we need to be able to respond to both
-- (server)
_⊓_ : {S : Set} (Φ₁ : S ▸ S) (Φ₂ : S ▸ S) → S ▸ S
Φ₁ ⊓ Φ₂ =
  record
  { B =  B Φ₁ *: B Φ₂
  ; C = λ { k (c1 , c2) →  C Φ₁ k c1 + C Φ₂ k c2 }
  ; d = λ { k (c1 , c2) (inl x) → d Φ₁ k c1 x 
          ; k (c1 , c2) (inr x) → d Φ₂ k c2 x
          } 
  }
  where open _▸_

-- add constant information J to the right hand side
growRight : {I J : Set } → I ▸ I → (I * J) ▸ (I * J)
growRight  x =
  record
  { B = λ { (i , _) → B x i }
  ; C = λ { (i , _) b → C x i b}
  ; d = λ { (i , j) b c → d x i b c , j }
  }
  where open _▸_

-- add constant information J to the left hand site 
growLeft : {I J : Set } → I ▸ I → (J * I) ▸ (J * I)
growLeft  x =
  record
  { B = λ { (_ , i) → B x i }
  ; C = λ { (_ , i) b → C x i b}
  ; d = λ { (j , i) b c → j , d x i b c }
  }
  where open _▸_

-- combine two interfaces that operate independently on separate
-- state.  Commands from one do not affect the other
_⊗_ : {I J : Set} → I ▸ I → J ▸ J → (I * J) ▸ (I * J)
_⊗_ {I} {J} x y with growRight {I} {J} x | growLeft {J} {I} y
_⊗_ {I} {J} x y | record { B = B ; C = C ; d = d } | record { B = B₁ ; C = C₁ ; d = d₁ } = record { B = {!!} ; C = {!!} ; d = {!!} }

--  Sequential composition flavors
-- note that we have folded these into the Free monad definitions. we do not need them
_>>○_ : ∀ {I J K} (Φ₁ : J ▸ I) → (Φ₂ : K ▸ J) → (K ▸ I)
_>>○_ Φ₁ Φ₂ =
  record
  { B =  (Φ₁ ○) (B Φ₂)
  ; C =  λ { a (b₁ , b₂) → Σ (C Φ₁ a b₁) (λ c₁ → C Φ₂ (d Φ₁ a b₁ c₁) (b₂ c₁)) }
  ; d =  λ { a (b₁ , b₂) (c₁ , c₂) → d Φ₂ (d Φ₁ a b₁ c₁) (b₂ c₁) c₂}
  }
  where open _▸_


_>>●_ : ∀ {I J K} (Φ₁ : J ▸ I) → (Φ₂ : K ▸ J) → (K ▸ I)
_>>●_ Φ₁ Φ₂ =
  record
    { B = (Φ₁ ●) (B Φ₂)
    ; C =  λ { s t → Σ (B Φ₁ s) (λ c1 → C Φ₂ (d Φ₁ s c1 (fst (t c1))) (snd (t c1)))} 
    ; d = λ { s t (c1 , r2) → d Φ₂ (d Φ₁ s c1 (fst (t c1))) ( snd (t c1)) r2 }
    }

  where open _▸_


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
    open Monad (free○-Monad (update (_+N_ 1)))


data Bool : Set where tt ff : Bool

postulate Char : Set
{-# BUILTIN CHAR Char #-}

postulate String : Set
{-# BUILTIN STRING String #-}


data WriteState : Set where
  opened closed : WriteState

data WriteCommand : WriteState → Set where
  openWrite  : (fileName : String) → WriteCommand closed
  writeChar  : Char                → WriteCommand opened
  closeWrite :                       WriteCommand opened

WriteResponse : (j : WriteState) (c : WriteCommand j) → Set
WriteResponse .closed (openWrite fileName) = WriteState
WriteResponse .opened (writeChar x) = Unit
WriteResponse .opened closeWrite = Unit

writeNext : (j : WriteState) (c : WriteCommand j) → WriteResponse j c → WriteState
writeNext .closed (openWrite fileName) r = opened
writeNext .opened (writeChar x) r = opened
writeNext .opened closeWrite r = closed

WRITE : WriteState ▸ WriteState
WRITE = record { B = WriteCommand ; C = WriteResponse ; d = writeNext }

data ReadState : Set where
  opened : (eof : Bool) → ReadState
  closed : ReadState

data ReadCommand : ReadState → Set where
  openRead : (fileName : String) → ReadCommand closed
  -- we can only read if we're not at EOF
  readChar : ReadCommand (opened tt)
  closeRead : {eof : Bool} → ReadCommand (opened eof)


ReadResponse : (j : ReadState) (c : ReadCommand j) → Set
ReadResponse .closed (openRead fileName) = Bool
ReadResponse .(opened tt) readChar = Maybe Char
ReadResponse .(opened _) closeRead = Unit

readNext : (j : ReadState) (c : ReadCommand j) → ReadResponse j c → ReadState
readNext .closed (openRead fileName) eof = opened eof
readNext .(opened tt) readChar Nothing =  opened tt
readNext .(opened tt) readChar (Just x) = opened ff
readNext .(opened _) closeRead r = closed 

READ : ReadState ▸ ReadState
READ = record { B = ReadCommand ; C = ReadResponse ; d = readNext }

-- Now we want to combine READ and WRITE for a CP interface


{-
openFile : Free○ FILES  (λ x → Unit) FileClosed
openFile = {!!}  -- step (OpenFile , (λ { t → stop unit ; f → stop  unit }))

readFile : Free○ FILES (λ x → Maybe Char) FileOpened
readFile = step (ReadFile , (λ y →  stop y))

closeFile : Free○ FILES (λ x → Unit) FileOpened
closeFile = step (CloseFile , (λ y → stop y) )


operations : Free○ FILES (λ x → Char) FileClosed
operations = openFile >>= λ { unit → {!!}} 
  where
    open Monad (free○-Monad FILES)
-}


data ResponseState : Set where
  StatusLineOpen HeadersOpen BodyOpen ResponseEnded : ResponseState
  

postulate Status Header Request : Set

data ResponseCommand : ResponseState → Set where
  WriteStatus : Status → ResponseCommand StatusLineOpen
  WriteHeader : Header → ResponseCommand HeadersOpen
  CloseHeaders : ResponseCommand HeadersOpen
  Send : (body : String) → ResponseCommand BodyOpen
  End : ResponseCommand BodyOpen
  -- some commands can always be executed

  GetRequestContext : {x : ResponseState} → ResponseCommand x


ResponseResponse : (i : ResponseState) (j : ResponseCommand i) → Set
ResponseResponse .StatusLineOpen (WriteStatus x) = Unit
ResponseResponse .HeadersOpen (WriteHeader x) = Unit
ResponseResponse .HeadersOpen CloseHeaders = Unit
ResponseResponse .BodyOpen (Send body) = Unit
ResponseResponse .BodyOpen End = Unit
ResponseResponse _         GetRequestContext = Request

ResponseNext : (i : ResponseState) (j : ResponseCommand i) → ResponseResponse i j → ResponseState
ResponseNext .StatusLineOpen (WriteStatus x) x₁ = HeadersOpen
ResponseNext .HeadersOpen (WriteHeader x) x₁ = HeadersOpen
ResponseNext .HeadersOpen CloseHeaders x = BodyOpen
ResponseNext .BodyOpen (Send body) x = BodyOpen
ResponseNext .BodyOpen End x =  ResponseEnded 
ResponseNext y   ReadBody x = y


RESPONSE : ResponseState ▸ ResponseState
RESPONSE = record { B = ResponseCommand ; C = ResponseResponse ; d = ResponseNext }

-- named after Robert Atkey
data AtKey {I : Set} ( X : Set) ( i : I) : I → Set where
  at : X → AtKey X i i

writeStatus : Status → Free○ RESPONSE (AtKey Unit HeadersOpen) StatusLineOpen
writeStatus x = step ((WriteStatus x) , (λ y → stop (at y)))

writeHeader : Header → Free○ RESPONSE  (AtKey Unit HeadersOpen) HeadersOpen
writeHeader x = step (WriteHeader x , (λ y → stop (at y )))

closeHeaders : Free○ RESPONSE (AtKey Unit BodyOpen) HeadersOpen
closeHeaders = step ( CloseHeaders , (λ y → stop (at y)) )

writeHeaders : Header → Free○ RESPONSE (AtKey Unit BodyOpen) HeadersOpen
writeHeaders x = writeHeader x >>= (λ { (at _) → closeHeaders})
  where open Monad (free○-Monad RESPONSE)

send : String → Free○ RESPONSE (AtKey Unit BodyOpen) BodyOpen
send x = step (Send x , (λ y → stop (at y )))

end : Free○ RESPONSE (AtKey Unit ResponseEnded) BodyOpen
end = step (End , (λ y → stop (at y)))

-- in any state, we can read the request context
getRequestContext : ∀ {k} → Free○ RESPONSE (AtKey Request k) k
getRequestContext = step (GetRequestContext , (λ { y → stop (at y) }))

respond : (body : String) → Free○ RESPONSE (AtKey Unit ResponseEnded) BodyOpen
respond body = send body >>= λ { (at x) → end }
  where open Monad (free○-Monad RESPONSE)



-- a server goes through the entire Webmachine statemachine
Server : Pow ResponseState → Set
Server X =  Free○ RESPONSE X ResponseEnded


handler : Server (λ x → Unit)
handler  = {!!}


