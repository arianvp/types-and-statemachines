
--------------------------------------------------------------------------------
-- Prelude
--------------------------------------------------------------------------------

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data Unit : Set where
  tt : Unit

data Empty : Set where

data Either (a b : Set) : Set where
  Inl : a -> Either a b
  Inr : b -> Either a b  

data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just : a -> Maybe a

data Bool : Set where
  True False : Bool

if_then_else : {a : Set} -> Bool -> a -> a -> a
if True then t else e = t
if False then t else e = e

[_,_] : {a b c : Set} -> (a -> c) -> (b -> c) -> (Either a b -> c)
[ f , g ] (Inl x) = f x
[ f , g ] (Inr x) = g x

const : {a b : Set} -> a -> b -> a
const = λ x y → x

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

data Sigma (a : Set) (b : a -> Set) : Set where
  _,_ : (x : a) -> b x -> Sigma a b

fsts : ∀ {a b} -> Sigma a b -> a
fsts (x , x₁) = x
snds : ∀ {a b} -> (x : Sigma a b) -> b (fsts x)
snds (x , x₁) = x₁

Pow : Set -> Set₁
Pow a = a -> Set

--------------------------------------------------------------------------------
-- Interaction structures
--------------------------------------------------------------------------------

record IS (S S' : Set)  : Set₁ where
  field
    C : S -> Set
    R : (s : S) -> C s -> Set
    n : (s : S) -> (c : C s) -> R s c -> S'

open IS

data Free {S : Set} (is : IS S S) (a : S -> Set)
  : S -> Set where
  Stop : ∀ {s : S} -> a s -> Free is a s
  Step : ∀ {s : S} ->
            (c : C is s) -> ((r : R is s c) -> Free is a (n is s c r)) ->
            Free is a s


--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

-- There exists a command such that all responses...
_○ : ∀ {S S'} -> (φ : IS S S') -> Pow S' -> Pow S
_○ record {C = C ; R = R ; n = n } P a =
   Sigma (C a) (\c -> (r : R a c) -> P (n a c r))

-- For all commands, there exists a response
_● : ∀ {S S'} -> (φ : IS S S') -> Pow S' -> Pow S
_● record { C = C ; R = R ; n = n } P a =
  (c : C a) -> Sigma (R a c) (\r -> P (n a c r))


_+_ : ∀ {S S'} -> IS S S' -> IS S S' -> IS S S'
record { C = C1 ; R = R1 ; n = n1 } +
  record { C = C2 ; R = R2 ; n = n2 } =
  record { C = \s -> Either (C1 s) (C2 s) ;
           R = \ { s (Inl x) → R1 s x ;
                   s (Inr x) → R2 s x } ;
           n = λ { s (Inl c) r  → n1 s c r ;
                   s (Inr c) r → n2 s c r }}

_⊕_ : ∀ {S S'} -> IS S S' -> IS S S' -> IS S S'
record { C = C1 ; R = R1 ; n = n1 }
  ⊕ record { C = C2 ; R = R2 ; n = n2 } =
  record { C = \s -> Pair (C1 s) (C2 s) ;
           R = \{s (c1 , c2) -> Either (R1 s c1) (R2 s c2) };
           n = \{ s (c1 , c2) (Inl x) → n1 s c1 x ;
                  s (c1 , c2) (Inr x) → n2 s c2 x }}

_>>○_ : ∀ {S1 S2 S3} -> IS S1 S2 -> IS S2 S3 -> IS S1 S3
is1 >>○ is2 = 
  record { C = (is1 ○) (λ x → C is2 x)  ;
                  -- give a command in C1 such that for each response,
                  -- and for each next state, there is a command C2
           R = \ { s (c1 , c2) → Sigma (R is1 s c1)
                                   (\r -> R is2 (n is1 s c1 r) (c2 r)) };
                   -- responses to both commands
           n = \ { s (c1 , c2) (r1 , r2) → n is2 (n is1 s c1 r1) (c2 r1) r2 }}
                   -- the next state in is2, based on both commands

_>>●_ : ∀ {S1 S2 S3} -> IS S1 S2 -> IS S2 S3 -> IS S1 S3
is1 >>● is2 =
  record {
    C = (is1 ●) (C is2) ;
        -- for each command in C1, there is a response s.t. we can
        --   give a command in C2 in the next state.
    R = \ {s t -> Sigma (C is1 s)
                    (\c1 -> R is2 (n is1 s c1 (fsts (t c1))) (snds (t c1)))};
    n = \ {s t (c1 , r2) -> n is2 (n is1 s c1 (fsts (t c1)))
                                  (snds (t c1)) r2}}

--------------------------------------------------------------------------------
--- Example
--------------------------------------------------------------------------------

data B (n : Nat) : Set where
  step : B n

data Error : Set where
  mkError : Nat -> Error -- add error string

data available? : Set where
  mkAvailable? : available?

data knownMethod? : Set where
  mkKnownMethod? : knownMethod?

WM : Set₁
WM = IS (Either Nat Error) (Either Nat Error) 

check : (err : Nat) -> WM
check err =
  record { C = \ { (Inl x) → Unit ;
                   (Inr err) → Empty }
         ; R = \ { (Inl x) c → Bool ; (Inr err₁) () }
         ; n = \ { (Inl x) c b → if b then Inl (Succ x) else (Inr (mkError err))
                 ; (Inr x) () b } }

available : WM
available = check 503

knownMethod : WM
knownMethod = check 501

uriTooLong : WM
uriTooLong = check 414

system = available >>● (knownMethod >>● uriTooLong)

test : Free system (\_ -> Unit) (Inl 0)
test =
  Step (λ c → True , (λ c₁ → True , tt))
        (λ { (tt , (tt , True)) → {!!};
             (tt , (tt , False)) → {!!} })

