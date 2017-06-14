{- This notebook is me going through Edwin Brady's state paper and following along.
I wrote it in agda such that I am forced to actually type out the examples in the paper
(that are usually incomplete and assume the reader knows how to fill in the gaps)
instead of copying over the Idris code from his library. I try to collect notes
of things I found perculiar, and to really grasp the paper fulyl

-}
postulate IO : Set → Set
postulate Char : Set

data Nat : Set where
  Z : Nat
  S : Nat → Nat
data Unit : Set where
  unit : Unit

-- From edwin brady's states paper
-- note that the Pure and Bind are encoded within the state datatype
module SimpleStates where
  data DoorState : Set where
    DoorOpen : DoorState
    DoorClosed  : DoorState


  data DoorCmd : Set -> DoorState -> DoorState -> Set₁ where
    Open : DoorCmd Unit DoorClosed DoorOpen
    Close : DoorCmd Unit DoorOpen DoorClosed
    RingBell : DoorCmd Unit DoorClosed DoorClosed
    Pure : { ty : Set } { state : DoorState } -> ty -> DoorCmd ty state state

    _>>=_ : {a b : Set} { state1 state2 state3 : DoorState} ->
      DoorCmd a state1 state2 -> (a -> DoorCmd b state2 state3) ->
      DoorCmd b state1 state3


  doorProg : DoorCmd Unit DoorClosed DoorClosed
  doorProg =
    RingBell >>= \_ ->
    Open     >>= \_ ->
    Close

data Bool : Set where
  True : Bool
  False : Bool 

const : {a b : Set} -> a -> b -> a
const x y = x

data DoorState : Set where
  DoorOpen : DoorState
  DoorClosed  : DoorState

data DoorResult : Set where
  Jammed : DoorResult
  OK : DoorResult

module DependentStates where
  

  -- we add an extra type parameter such that the next state can depend
  -- on the result of the previous stateful computation
  data DoorCmd : (a : Set) -> DoorState -> (a -> DoorState) -> Set₁ where
    Open : DoorCmd DoorResult DoorClosed (λ { Jammed → DoorClosed ; OK → DoorOpen})
    Close : DoorCmd Unit DoorOpen (const DoorClosed)
    RingBell : DoorCmd Unit DoorClosed (const DoorClosed)
    Pure : { ty : Set } { state : DoorState } -> ty -> DoorCmd ty state (const state)

    _>>=_ : {a b : Set}
          → {s₁ : DoorState }
          → {s₂ : a → DoorState }
          → {s₃ : b → DoorState }
          → DoorCmd a s₁ s₂ → ((x : a) → DoorCmd b (s₂ x) s₃) → DoorCmd b s₁ s₃


  doorProg : DoorCmd Bool DoorClosed (const DoorClosed)
  doorProg =
    RingBell >>= λ _ →
    Open >>= λ
    { Jammed →
        Pure False
    ; OK →
        Close >>= λ _ → Pure True
    }


  -- Doorprog is a description of interactions with a door,
  -- what is left is an interpetation.

  run : (t : Set) ( sᵢ : DoorState) (f : t → DoorState) (jam_time : Nat) → DoorCmd t sᵢ f → IO t
  run = {!!}


{- There are some nice properties of describing state trasnstions this way.
Edwin notes that doorProg enforces that the program starts in a Closed state
and ends in a Closed state. This allows for only a small subset of state descriptions to
typecheck, eliminating programs that do not adhere to the protocol that is described in the
types.

However, this approach is not scalable. 

We want to define multiple state transitions like DoorCmd independently of eachother
and then allow to combine them into larger state transition systems.

We want to define different implementations for such a state transisition system (Free monads?)

We want to associate implementations with resources which store the underlying state of a
system

We want to have some kind of combinators to form a hierachy of states. Making it possible
to implement a high level State diagram (Say HTTP) based on a lower level state diagram
(say TCP)
-}


-- we observe that the signature of a state machine is the following type:

module States where
  SM_sig : Set → Set₁
  SM_sig s = (τ : Set) → s → (τ → s) → Set

  -- a statemachine over some state alphabet Σ
  record SM (S : Set) : Set₁ where
    constructor MkSM
    field
      -- an initial state
      init : S
      -- a predicate that defines the set of final states
      final : S → Set
      -- a set of operations which define our state transitions
      operations : SM_sig S
      -- a set of operations on how to create new state machines
      -- from existing states.  (Explained in section 4? dunno what this is so far)
      creators : SM_sig S


  -- lets return to our door example, and implement it in this new framework

  data DoorOp : SM_sig DoorState where
    Open : DoorOp DoorResult DoorClosed (λ { OK → DoorOpen ; Jammed → DoorClosed })
    Close : DoorOp Unit DoorOpen (const DoorClosed)
    RingBell : DoorOp Unit DoorClosed (const DoorClosed)


  -- A predicate that checks if something is a final state
  data DoorFinal : DoorState → Set where
    ClosedFinal : DoorFinal DoorClosed

  -- the empty state machine Operation
  data None : {τ : Set} → SM_sig τ where
  
  Door : SM DoorState
  Door = MkSM DoorClosed DoorFinal DoorOp None
