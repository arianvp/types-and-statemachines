-- interaction structure
interface IS (state : Type) where
  C : state -> Type
  R : (s : state) -> C s -> Type
  n : {s : state} -> (c : C s) -> (r : R s c) -> state

-- Type indexed free monad  
data Free : state -> (a : state -> Type) -> Type where
  Pure : IS state => {s : state} -> a s -> Free s a
  Step : IS state => {s : state} -> (c : C s)  -> ((r : R s c) -> Free (n c r) a) -> Free s a
  

namespace OpenMayFail
  data Result = Fail | OK
  data State = Opened | Closed

  data Cmd : State -> Type where
    Open : Cmd Closed
    Close : Cmd Opened
    Read : Cmd Opened
    


  IS State where
    C = Cmd
    R _ Open =  Result
    R _ Close = ()
    R _ Read = Maybe Char
    n Open Fail = Closed
    n Open OK = Opened
    n Close r = Closed
    n Read r = Opened
    

  pure : {s : State} -> a s -> Free s a
  pure = Pure
  
  (>>=) : {s : State} -> Free s a -> ({s' : State} -> a s' -> Free s' b) -> Free s b
  (Pure x) >>= f = f x
  (Step c k) >>= f = Step c (\r => k r >>= f)
 
  
  openFile : Free Closed ?a
  openFile = Step OpenMayFail.Open ?b
  
  
