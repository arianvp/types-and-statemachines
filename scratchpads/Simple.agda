-- COPYRIGHT Wouter Swierstra

data Free (C : Set) (R : C -> Set) (a : Set) : Set where
  Stop : a -> Free C R a
  Step : (c : C) -> (R c -> Free C R a) -> Free C R a

return : ∀ {a C R} -> a -> Free C R a
return = Stop

_>>=_ : ∀ {a b C R} -> Free C R a -> (a -> Free C R b) -> Free C R b
Stop x >>= f = f x
Step c x >>= f = Step c (\r -> x r >>= f)

-- Exercise for the reader: Implement a simple example, such as
--   ReadChar/PutChar, or OpenFile/CloseFile/ReadChar

