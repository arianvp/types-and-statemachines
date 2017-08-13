module  InteractionStructures 

-- In Idris, we can define types easily:

-- so how do we model the the fact that we can choose a type,
-- based on the value of some other type? We can simply

Pow : Type -> Type
Pow x = x -> Type 

mapPow : (x -> y) -> (Pow y -> Pow x)
mapPow g f = f . g
 

Always : (P : Pow i) -> Type
Always {i} P = {j : i} -> P j
 
infixr 3 :->
infixr 3 :*
infixr 3 :+
(:->) : (S, T : Pow i) -> Pow i
(:->) S T i  = S i -> T i
(:*) : (S, T : Pow i) -> Pow i
(:*) S T i  = (S i , T i)
(:+) : (S, T : Pow i) -> Pow i
(:+) S T i  = Either (S i)  (T i)


namespace Normal
    data Free : (Type -> Type) -> (Type -> Type) where
      Stop : x -> Free f x
      Step : f (Free f x) -> Free f x
    
      
namespace Indexed
  interface Functor (f : Pow w -> Pow w) where
    map : (x i -> y i) -> f x i -> f y i

    
  interface Functor f => Monad (f : Pow w -> Pow w) where
    pure : x i -> f x i
    (>>=) : f x i -> (x i -> f y i) -> f y i
    
  data Free : (Pow w -> Pow w) -> (Pow w -> Pow w) where
    Stop : x i -> Indexed.Free f x i
    Step : f (Indexed.Free f x) i -> Indexed.Free f x i

  Indexed.Functor f => Indexed.Functor (Indexed.Free f) where
    map g val = assert_total (case val of
                                   (Stop x) => Stop (g x)
                                   (Step x) => Step (Indexed.map (Indexed.map g) x))

  Indexed.Functor f => Indexed.Monad (Indexed.Free f) where
    pure = Stop
    m >>= f = assert_total (case m of
                              (Stop x) => f x
                              (Step x) => Step (Indexed.map (>>= f) x))
  
record InteractionStructure (v : Type) (w : Type) where
  constructor MkInteractionStructure
  Cmd : Pow v
  Resp : (state : v) -> (cmd : Cmd state) -> Type
  nextState : (state : v) -> (cmd : Cmd state) -> (resp : Resp state cmd) -> w
  

ISC : InteractionStructure i j -> Pow j -> Pow i
ISC is p i = ?help

data CounterCommand : Pow Nat where
  Reset : CounterCommand x
  Decrease : CounterCommand (S x)
  Increase : CounterCommand x
  
-- for now we assume we always receive a new Nat  
Response : (a : Nat) -> Pow (CounterCommand a)
Response a b = Nat
  
  
  
    
 
 
 
 
