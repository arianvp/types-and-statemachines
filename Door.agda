-- This module shows that interaction structures have
-- similar strength to States, and that States bring no
-- new added benefits.

open import Prelude
open import InteractionStructures

-- We start off with two examples. Door and State


-- the universe of types we can store in a variable
data U : Set where
  NAT : U
  CHR : U

el : Pow U
el NAT = Nat
el CHR = Char


data VarCmd : Pow U where
  Get : {t : U} → VarCmd t
  Put :  {s : U} (t : U) → el t → VarCmd s


VarResp  : (a : U) → VarCmd a → Set
VarResp a Get = el a
VarResp a (Put b x) = Unit


varNext : (a : U) → (b : VarCmd a) → VarResp a b → U
varNext a Get x = a
varNext a (Put b k) x = b



VAR : U ▸ U
VAR = record
  { Cmd = VarCmd
  ; Resp = VarResp
  ; next = varNext
  }





-- very simple version of sequential composition
-- We get a NAT from VAR1 and PUT it in VAR2
-- finally, we return the value from the First operation executed
TWO_VARS : U ▸ U
TWO_VARS = VAR >>○ VAR

copy : Free○ TWO_VARS (AtKey (el NAT) NAT) NAT
copy = step ((Get , Put NAT) , λ { (getRes₁ , putRes₁) → stop (at getRes₁)})

data Tree (a : Set) : Set where
 Empty : Tree a
 Node : Tree a → a → Tree a → Tree a



 

get : Free○ VAR (AtKey (el NAT) NAT) NAT
get = step (Get , λ y → stop (at y))


put : {s : U} (t : U) → (el t) → Free○ VAR (AtKey Unit t) s
put {s} t x = step (Put t x , λ y → stop (at y))

-- an example program
tag : ∀ {a} → Tree a → Free○ VAR (AtKey (Tree (el NAT × a)) NAT) NAT
tag Empty = stop (at Empty)
tag (Node left val right) =
  tag left >>= λ { (at left') →
  get >>= λ { (at t) →
  put NAT (suc t) >>=  λ { (at x) →
  tag right >>= λ { (at right') →
  stop (at (Node left' (t , val) right'))}}}}
  where open IxMonad (free○-IxMonad VAR)


data DoorState : Set where
  DoorOpened DoorClosed : DoorState

data DoorCmd : Pow DoorState where
  Open : DoorCmd DoorClosed
  Close : DoorCmd DoorOpened
  RingBell : DoorCmd DoorClosed

data DoorResult : Set where
  Jammed OK : DoorResult

DoorResp : (s : DoorState) → DoorCmd s → Set
DoorResp .DoorClosed Open = DoorResult
DoorResp .DoorOpened Close = Unit
DoorResp .DoorClosed RingBell = Unit

doorNext : (s : DoorState) (c : DoorCmd s) → DoorResp s c → DoorState
doorNext .DoorClosed Open Jammed = DoorClosed
doorNext .DoorClosed Open OK = DoorOpened
doorNext .DoorOpened Close unit = DoorClosed
doorNext .DoorClosed RingBell unit = DoorClosed


DOOR : DoorState ▸ DoorState
DOOR = record { Cmd = DoorCmd ; Resp = DoorResp ; next = doorNext }


ringBell : Free○ DOOR (AtKey Unit DoorClosed) DoorClosed
ringBell = step ( RingBell , λ { unit → stop (at unit)})



-- at each step, you choose which effect to take either DOOR or VAR
-- in the states paper, we do this by a witness into a Heterogenous list,
-- which is similar to a  n-ary union. We take a binary union
doorProgCount : Free○ (DOOR ⊗ VAR) (AtKey Unit (DoorClosed , NAT)) (DoorClosed , NAT)
doorProgCount =
  step (inl RingBell , λ { unit →
  step (inl Open , λ {
    Jammed → stop (at unit) ;
    OK →
      step (inr Get , λ n →
      step (inr (Put NAT (suc n)) , λ y →
      step (inl Close , λ { unit → stop (at unit)})))})})




  


data DoorCmd1 : Pow DoorState where
  Open : DoorCmd1 DoorClosed
  RingBell : DoorCmd1 DoorClosed


DoorResp1 : (s : DoorState) → DoorCmd1 s → Set
DoorResp1 .DoorClosed Open = DoorResult
DoorResp1 .DoorClosed RingBell = Unit

doorNext1 : (s : DoorState) (c : DoorCmd1 s) → DoorResp1 s c → DoorState
doorNext1 DoorOpened () x
doorNext1 DoorClosed Open Jammed = DoorClosed
doorNext1 DoorClosed Open OK = DoorOpened
doorNext1 DoorClosed RingBell unit = DoorClosed


DOOR_OPENER : DoorState ▸ DoorState
DOOR_OPENER = record { Cmd = DoorCmd1 ; Resp = DoorResp1 ; next = doorNext1 }


-- another component, that can only close doors
data DoorCmd2 : Pow DoorState where
  Foo : DoorCmd2 DoorClosed
  Close : DoorCmd2 DoorOpened

DoorResp2 : (s : DoorState) → DoorCmd2 s → Set
DoorResp2 .DoorOpened Close = Unit
DoorResp2 .DoorClosed Foo = Unit

doorNext2 : (s : DoorState) (c : DoorCmd2 s) → DoorResp2 s c → DoorState
doorNext2 .DoorOpened Close unit = DoorClosed
doorNext2 .DoorClosed Foo unit = DoorOpened

DOOR_CLOSER : DoorState ▸ DoorState
DOOR_CLOSER = record { Cmd = DoorCmd2 ; Resp = DoorResp2 ; next = doorNext2 }



-- Say we have one state machine that can only open doors
-- and another that only is responsible for closing
-- then we can combine them to create an entire state machine:
DOOR2 : DoorState ▸ DoorState
DOOR2 = DOOR_OPENER >>○ DOOR_CLOSER

doorProgCount2 : Free○ (DOOR2 ⊗ VAR) (AtKey Unit (DoorClosed , NAT)) (DoorClosed , NAT)
doorProgCount2 = step (inl (RingBell , λ { unit → Foo}) , λ { (unit , unit) → {!!}})
  {-
  step (inl (inl RingBell) , λ { unit →
  step (inl (inl Open) , λ {
    Jammed → stop (at unit) ;
    OK →
      step (inl {!!} , {!!})})})
   -}



data Role : Set where
  Client Server : Role


data SocketState : Set where
  Closed Ready Bound Connected Listening : SocketState
  Open : Role → SocketState

data CloseOK : Pow SocketState where
  CloseOpen : {role : Role} → CloseOK (Open role)
  CloseListening : CloseOK Listening


data NetCmd : Pow SocketState where
  Socket : Role → NetCmd Closed
  Bind : String → Nat → NetCmd Ready
  Listen : NetCmd Bound
  Connect : String → Nat → NetCmd Ready
  Close : ∀ {s} → CloseOK s → NetCmd s
  Send : ∀ {r} → String → NetCmd (Open r)
  Recv : ∀ {r} → NetCmd (Open r)
  

NetResp : (s : SocketState) (c : NetCmd s) → Set
NetResp .Closed (Socket x) =  String + Unit
NetResp .Ready (Bind x x₁) = String + Unit
NetResp .Bound Listen = String + Unit
NetResp .Ready (Connect x x₁) =  String + Unit
NetResp x (Close x₁) = Unit
NetResp .(Open _) (Send x) = String + Unit
NetResp .(Open _) Recv = String + Unit

netNext : (s : SocketState) (c : NetCmd s) (r : NetResp s c) → SocketState
netNext .Closed (Socket x) (inl x₁) = Closed
netNext .Closed (Socket x) (inr x₁) = Ready
netNext .Ready (Bind x x₁) (inl x₂) = Closed
netNext .Ready (Bind x x₁) (inr x₂) = Bound
netNext .Bound Listen (inl x) = Closed
netNext .Bound Listen (inr x) = Listening
netNext .Ready (Connect x x₁) (inl x₂) = Closed
netNext .Ready (Connect x x₁) (inr x₂) = Open Client
netNext x (Close x₁) unit = Closed
netNext (Open r) (Send x) (inl x₁) = Closed
netNext (Open r) (Send x) (inr x₁) = Open r
netNext (Open r) Recv (inl x) = Closed
netNext (Open r) Recv (inr x) = Open r


data List (a : Set) : Set where
  Nil : List a
  _∷_ : a → List a → List a
  

data Card : Set where
  Arian : Card
data CartItem : Set where
  Bread Butter : CartItem
  
data CheckoutState : Set where
  NoItems : CheckoutState
  HasItems : List CartItem → CheckoutState
  NoCard : List CartItem → CheckoutState
  CardSelected : List CartItem → Card → CheckoutState
  CardConfirmed : List CartItem → Card → CheckoutState
  OrderPlaced : CheckoutState


  
data ShopCommand : Pow CheckoutState where
  Select : CartItem → ShopCommand NoItems
  Select1 : ∀ {x} → CartItem → ShopCommand (HasItems x)

-- TODO make state implicit
-- everything succeeds trivially
ShopResp : (a : CheckoutState) → Pow (ShopCommand a)
ShopResp _ (Select x) = Unit
ShopResp _ (Select1 x₁) = Unit

shopNext : (a : CheckoutState) (b : ShopCommand a) → ShopResp a b → CheckoutState
shopNext .NoItems (Select x) unit = HasItems (x ∷ Nil)
shopNext (HasItems xs) (Select1 x₁) unit = HasItems ( x₁ ∷ xs )
--shopNext (HasItems xs) Checkout unit = NoCard xs 

SHOP : CheckoutState ▸ CheckoutState
SHOP = record
  { Cmd = ShopCommand
  ; Resp = ShopResp
  ; next = shopNext
  }

data CheckoutCommand : Pow CheckoutState where
  Checkout : ∀ {x} → CheckoutCommand (HasItems x)
  SelectCard : ∀ {x} → (c : Card) → CheckoutCommand (NoCard x)
  Confirm : ∀ {x} {c : Card} → CheckoutCommand (CardSelected x c)
  PlaceOrder : ∀ {x} {c : Card} → CheckoutCommand (CardConfirmed x c)
  -- TODO add a constraint on cancelable states
  --Cancel : ∀ s → CheckoutCommand s

CheckoutResp : (a : CheckoutState) → CheckoutCommand a → Set
CheckoutResp _ (Checkout) = Unit
CheckoutResp _ (SelectCard _) = Unit
CheckoutResp _ Confirm = Unit
CheckoutResp _ PlaceOrder = Unit
--CheckoutResp a (Cancel .a) = Unit

checkoutNext : (a : CheckoutState) (b : CheckoutCommand a) → CheckoutResp a b → CheckoutState
checkoutNext (HasItems x) Checkout unit = NoCard x
checkoutNext (NoCard xs) (SelectCard c) x = CardSelected xs c
checkoutNext (CardSelected c xs) Confirm x = CardConfirmed c xs
checkoutNext (CardConfirmed c xs) PlaceOrder x = OrderPlaced



CHECKOUT : CheckoutState ▸ CheckoutState
CHECKOUT = record { Cmd = CheckoutCommand ; Resp = CheckoutResp ; next = checkoutNext }



THE_SHOP : CheckoutState ▸ CheckoutState
THE_SHOP = SHOP >>○ CHECKOUT

combine : ∀ {i o i' o'} → Free○ SHOP o i → Free○ CHECKOUT o' i' → Free○ (SHOP >>○ CHECKOUT) o' i
combine (stop x₁) (stop x₂) = stop {!!}
combine (stop x₁) (step x₂) = {!!}
combine (step x₁) (stop x₂) = {!!}
combine (step x₁) (step x₂) = {!!}

-- We have a shopping session ending in HasItems
session : Free○ SHOP (AtKey Unit (HasItems (Bread ∷ (Butter ∷ Nil)))) NoItems
session = step (Select Butter , λ { unit → step (Select1 Bread , λ { unit → stop (at unit)})})


-- We have a checkout session, which starts by Calling Checkout and ends with PlaceOrder
session2 : Free○ CHECKOUT (AtKey Unit OrderPlaced) (HasItems (Bread ∷ (Butter ∷ Nil)))
session2 =
             step (Checkout ,
  λ { unit → step ((SelectCard Arian) ,
  λ { unit → step (Confirm ,
  λ { unit → step (PlaceOrder ,
  λ { unit → stop (at unit)}) })})})


-- now the question follows, can we combine session and session2?
session3 : Free○ SHOP (AtKey Unit (HasItems (Bread ∷ (Butter ∷ Nil)))) NoItems
         → Free○ CHECKOUT (AtKey Unit OrderPlaced) (HasItems (Bread ∷ (Butter ∷ Nil)))
         → Free○ (SHOP >>○ CHECKOUT) (AtKey Unit OrderPlaced) NoItems
session3 (stop ()) (stop x₁)
session3 (stop ()) (step x₁)
session3 (step (fst₁ , snd₁)) (stop ())
session3 (step (Select x , snd₁)) (step (Checkout , snd₂)) = step (((Select x) , λ y → {!Checkout!}) , {!!})


-- this works, but it only makes sense to make one step, where we immediately move to  CHECKOUT
-- Then the next step we're stuck, as we end up in a State that is not covered by the SHOP
-- State machine, but we again need to provide a step
session4 : Free○ (SHOP >>○ CHECKOUT) (AtKey Unit OrderPlaced) NoItems
session4 =
                      step (((Select Bread) , λ { unit → Checkout}) ,
  λ { (unit , unit) → step (({! here is no possibility!} , λ y → {!!}) , {!!}) })




-- instead, angelic choice is probably a lot more interesting,
-- at any point you _choose_ which statemachine you're in,
-- but if you choose too early, you won't be able to make any progress,
-- as you're not yet in a state in which CHECKOUT is possible
session5 : Free○ (SHOP ⊔ CHECKOUT) (AtKey Unit OrderPlaced) NoItems
session5 =
  step ((inl (Select Bread)) , λ { unit →
  step (inl (Select1 Butter) , λ { unit →
  step (inr Checkout , λ { unit →
  -- if you would now select inl then there are no introduction forms
  -- because we're in a state that the SHOP statemachine does not support
  -- step (inl {!!} , {!!})})})})
  -- however, the person himself makes this active choice, instead
  -- of it being infered.. which is a shame.
  -- but I do feel that Angelic Choice _is_ the structure we're looking for
  step (inr (SelectCard Arian) , λ { unit →
  step ((inr Confirm) , λ { unit →
  step ((inr PlaceOrder) , λ { unit → stop (at unit)})})})})})})

-- what if we have two pre-existing sessions? , then we can simply take a natural transformation?

sessionTrans : ∀ {a}
             → Free○ SHOP (AtKey Unit (HasItems (Bread ∷ Nil))) a
             → Free○ CHECKOUT (AtKey Unit (HasItems (Bread ∷ Nil))) OrderPlaced
             → Free○ (SHOP ⊔ CHECKOUT) (AtKey Unit OrderPlaced) a
      
sessionTrans (stop (at x)) (stop ())
sessionTrans (stop (at x)) (step (() , snd₁))
sessionTrans (step (Select Bread , snd₁)) (stop ())
sessionTrans (step (Select Butter , snd₁)) (stop ())
sessionTrans (step (Select1 x₂ , snd₁)) (stop ())
sessionTrans (step (Select x , snd₁)) (step (() , snd₂))
sessionTrans (step (Select1 x₁ , snd₁)) (step (() , snd₂))

-- Also, I want to decide at any time I'm done with shopping and continue on the checkout
-- however >>○ seems not be what we're looking for?

-- Computatie in Shop  X -> Y        Computatie Checkout  Y -> (Z | X)  Computatie Shop X -> Y





data TrivState : Set where
  One : TrivState
  Two : TrivState
  Finished : TrivState


data OneCmd : Pow TrivState where
  oneAgain : OneCmd One
  letsGoToTwo : OneCmd One

-- We define the possible states that the server could return from our command
OneResp : ∀ a → OneCmd a → Set
OneResp _ oneAgain = Unit
OneResp _ letsGoToTwo = Unit

oneNext : ∀ a (b : OneCmd a) → (OneResp a b) → TrivState
oneNext _ oneAgain unit = One
oneNext _ letsGoToTwo unit = Two

ONE : TrivState ▸ TrivState
ONE = record
  { Cmd =  OneCmd
  ; Resp =  OneResp
  ; next =  oneNext
  }


data TwoCmd : Pow TrivState where
  twoAgain : TwoCmd Two
  finish : TwoCmd Two


TwoResp : ∀ a → TwoCmd a → Set
TwoResp _ twoAgain = Unit
TwoResp _ finish = Unit

twoNext : ∀ a (b : TwoCmd a) → (TwoResp a b) → TrivState
twoNext _ twoAgain unit = Two
twoNext _ finish a = Finished

TWO : TrivState ▸ TrivState
TWO = record
  { Cmd =  TwoCmd
  ; Resp =  TwoResp
  ; next =  twoNext
  }


FIN : TrivState ▸ TrivState
FIN = abort

-- two very trivial state machines

ones : Free○ ONE (AtKey Unit One) One
ones = {!!} 

transfer : Free○ ONE (AtKey Unit Two) One
transfer = {!!}

twos : Free○ TWO (AtKey Unit Two) Two
twos = step (twoAgain , λ { unit → stop (at unit)})

-- at every step we also need to do a step in the other state machine
done : Free○ (TWO >>○ skip) (AtKey Unit Finished) Two
done = step ((twoAgain , (λ y → unit)) , λ { (unit , snd₁) →  step ((finish , λ y → unit) , λ { (fst₁ , snd₁) → stop (at unit)}) })

-- we cant proceed, we can only stop
lol : Free○ abort (AtKey Unit Finished) Finished
lol =  stop (at unit)
