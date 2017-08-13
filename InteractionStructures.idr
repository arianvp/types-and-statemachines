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


-- Functors over indexed sets
interface IxFunctor (f : Pow i -> Pow j) where
  mapIx : Always (x :-> y) -> Always (f x :-> f y)
  
infixl 3 =<<
interface IxFunctor f => IxMonad (f : Pow w -> Pow w) where
  pure : Always (p :-> f p)
  (=<<) : Always (p :-> f q) -> Always (f p :-> f q)


data Free : (f : Pow i -> Pow j) -> (x : Pow i) -> (j : i) -> Type where
  Stop : (x :-> Free f x) i
  Step : (f (Free f x) :-> Free f x) i


record InteractionStructure i j (v : Pow i) where
  constructor MkInteractionStructure
  Command : Pow j
  Response : (a : j) -> Pow (Command a)
  nextState : (a : j) -> (b : Command a) ->  Response a b -> i
  view : (a : j) -> (b : Command a) -> (c : Response a b) -> v (nextState a b c)
  


data CounterCommand : Pow Nat where
  Reset : CounterCommand x
  Decrease : CounterCommand (S x)
  Increase : CounterCommand x
  
-- for now we assume we always receive a new Nat  
Response : (a : Nat) -> Pow (CounterCommand a)
Response a b = Nat
  
  
  
    
 
 
 
 
