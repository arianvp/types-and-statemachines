
-- The basics --

postulate
  FilePath : Set
  Char : Set
  
data Unit : Set where
  tt : Unit

data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just : a -> Maybe a

data Free (S : Set)  -- the set of states (e.g. Open | Closed)
          (C : S -> Set) -- the set of commands (openFile, closeFile, ..)
          (R : (s : S) -> C s -> Set) -- the responses to commands
                                     -- (the value you're expecting in reply)
          (n : ∀ {s} -> (c : C s) -> (r : R s c) -> S) -- compute the next state
          (A : S -> Set) -- the return value
          : S -> Set where
  Stop : ∀ {s : S} -> A s -> Free S C R n A s -- return a value of type A s
  Step : ∀ {s : S} ->
            -- issue the command c and handle the response c
            (c : C s) -> ((r : R s c) -> Free S C R n A (n c r)) ->
            Free S C R n A s

-- A worked out example
module OpenAlwaysSucceeds where
  data State : Set where
    Closed : State
    Open : State

  data C : State -> Set where
    Open : C Closed
    Close : C Open
    Read : C Open

  R : ∀ (s : State) -> C s -> Set
  R _ Open = Unit
  R _ Close = Unit
  R _ Read = Maybe Char

  n : ∀ {s : State} -> (c : C s) -> R s c -> State
  n Open r = Open
  n Close r = Closed
  n Read r = Open

  -- A type synonym for the free monad du jour
  m : (State -> Set) -> State -> Set
  m = Free State C R n

  -- Return and bind as 'usual'
  return : ∀ {a : State -> Set} {s : State} -> a s -> m a s
  return = Stop

  _>>=_ : ∀ {a b : State -> Set} {s : State} ->
    m a s -> (∀ {s'} -> a s' -> m b s') -> m b s
  (Stop x) >>= f = f x
  (Step c k) >>= f = Step c (\r -> k r >>= f)

  -- This one is useless in practice...
  _>>_ : ∀ {a b : State -> Set} {s : State} ->
    (c : m a s) -> (∀ {s'} -> m b s') -> m b s
  c >> f = c >>= \_ -> f

module Stuck where
  open OpenAlwaysSucceeds
  -- If you do the 'naive' thing and ignore the state parameter,
  -- you can get stuck quite easily.

  K : Set -> State -> Set
  K a _ = a

  read : m (K (Maybe Char)) Open
  read = Step Read Stop

  openFile : m (K Unit) Closed
  openFile = Step Open (λ r → Stop tt)

  closeFile : m (K Unit) Open
  closeFile = Step Close (λ r → Stop tt)

  stuck : m (K Char) Closed
  stuck = openFile >>
         {!!} -- at this point you no longer know that the current state is Open

module Bob where
  open OpenAlwaysSucceeds
  
  -- Tag a value with the current state
  data at (x : State) (a : Set) : State -> Set where
    V : a -> at x a x

  -- starting from an closed file, open it
  openFile : m (at Open Unit) Closed
  openFile = Step Open (λ r → Stop (V tt))

  -- Starting from a open file, close it
  closeFile : m (at Closed Unit) Open
  closeFile = Step Close (λ r → Stop (V tt))

  -- read leaves the file open
  read : m (at Open (Maybe Char)) Open
  read = Step Read (\r -> Stop (V r))

  -- now we only have to worry about the state that we're in
  -- the pattern matching lambdas and implicits are ugly...
  -- can this be improved?
  not-stuck : m (at Closed (Maybe Char)) Closed
  not-stuck = openFile >>= \ { {Open} (V x) ->
              read >>= (\ { {Open} (V y) ->
              closeFile >>= (\ { {Closed} (V z) ->
              return (V y)})})}

  read-before-open : m (at Closed (Maybe Char)) Closed
  read-before-open = {!read!} -- is not accepted
module OpenMayFail where

  data State : Set where
    Closed : State
    Open : State

  data C : State -> Set where
    Open : C Closed
    Close : C Open
    Read : C Open

  R : ∀ (s : State) -> C s -> Set
  R _ Open = State -- Now open returns a new state, depending on
                   -- whether it succeeded or not
  R _ Close = Unit
  R _ Read = Maybe Char

  n : ∀ {s : State} -> (c : C s) -> R s c -> State
  n Open res = res   -- now check whether the file opened or not
  n Close r = Closed
  n Read r = Open

  -- A type synonym for the free monad du jour
  m : (State -> Set) -> State -> Set
  m = Free State C R n

  -- Return and bind as 'usual'
  return : ∀ {a : State -> Set} {s : State} -> a s -> m a s
  return = Stop

  _>>=_ : ∀ {a b : State -> Set} {s : State} ->
    m a s -> (∀ {s'} -> a s' -> m b s') -> m b s
  (Stop x) >>= f = f x
  (Step c k) >>= f = Step c (\r -> k r >>= f)

  -- This one is useless in practice...
  _>>_ : ∀ {a b : State -> Set} {s : State} ->
    (c : m a s) -> (∀ {s'} -> m b s') -> m b s
  c >> f = c >>= \_ -> f


  -- Tag a value with the current state
  data at (x : State) (a : Set) : State -> Set where
    V : a -> at x a x

  -- starting from an closed file, try to open it
  openFile : m (\b -> at b Unit b) Closed
  openFile =
    Step Open (\r -> Stop (V tt))

  -- Starting from a open file, close it
  closeFile : m (at Closed Unit) Open
  closeFile = Step Close (λ r → Stop (V tt))

  -- read leaves the file open
  read : m (at Open (Maybe Char)) Open
  read = Step Read (\r -> Stop (V r))

  -- now we only have to worry about the state that we're in
  -- the pattern matching lambdas and implicits are ugly...
  -- can this be improved?
  not-stuck : m (at Closed (Maybe Char)) Closed
  not-stuck = openFile >>= (\ { {Open} (V x) → {!success!!} ;
                                {Closed} (V x) → {!handle failure!} })
              -- {!now we need to check whether the open succeeded
              -- or not, before we can proceed; this is more general
              -- than the usual parametrized monad representation.!}

  


