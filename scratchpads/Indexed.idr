-- %default total
-- interaction structure
record IS where
  constructor MkIS
  
  S : Type
  C : S -> Type
  R : (s : S) -> C s -> Type
  N : {s : S} -> (c : C s) -> (r : R s c) -> S
  
  

data Free : (is : IS) -> (a : S is -> Type) -> (S is) -> Type where
  Stop : a s -> Free is a s
  Step : (c : C is s) -> ((r : R is s c) -> Free is a (N is c r)) -> Free is a s

namespace OpenMayFail
  data Result = Fail | OK
  data State = Opened | Closed

  data Cmd : State -> Type where
    Open : Cmd Closed
    Close : Cmd Opened
    Read : Cmd Opened
  
   

  r : (s : State) -> Cmd s -> Type
  r Closed Open = Result
  r Opened Close = ()
  r Opened Read = Maybe Char
  
  n : {s : State} -> (c : Cmd s) -> r s c -> State
  n Open Fail = Closed
  n Open OK = Opened
  n Close res = Closed
  n Read r = Opened

  is : IS
  is = MkIS State Cmd r n
  
  m : (State -> Type) -> State -> Type
  m a = Free is a
  
  pure' : a s -> m a s
  pure' = Stop
  

  data At : (x : State) -> (a : Type) -> State -> Type where
    V : a -> At x a x


  openFile : m (\b => At b () b) Closed
  openFile = Step Open (\r => Stop (V ()))
  
  closeFile : m (\b => At Closed () b) Opened
  closeFile = Step Close (\r => Stop (V ()))
  
  read : m (At Opened (Maybe Char)) Opened
  read = Step Read (\r => Stop (V r))
  

  pure : a -> m (At s a) s
  pure {s} x = Stop (V x)
      
  (>>=) : m a s -> ((xy : DPair State a) -> m b (fst xy)) -> m b s
  (>>=) (Stop {s} x) f = f (s ** x)
  (>>=) (Step  c k) f = Step c (\r => k r >>= f)

  -- I had to comment %default total because
  -- Idris' totally checker is not smart enough to figure out that these
  -- pattern matches are exhaustive
  notStuck : m (At Closed (Maybe Char)) Closed
  notStuck = do
    (Opened ** V ()) <- openFile | (Closed ** v2) => pure Nothing
    (Opened ** V c) <- read
    (Closed ** V ()) <- closeFile
    pure c

  
