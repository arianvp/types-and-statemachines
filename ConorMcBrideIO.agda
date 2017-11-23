module ConorMcBrideIO where

open import Prelude
open import InteractionStructures


-- States

data WriteState : Set where
  opened closed : WriteState



data WriteCommand : Pow WriteState where
  openWrite : (fileName : String) → WriteCommand closed
  writeChar : Char → WriteCommand opened
  closeWrite : WriteCommand opened


WriteResponses :  (j : WriteState) (c : WriteCommand j) → Set
WriteResponses .closed (openWrite fileName) = WriteState
WriteResponses .opened (writeChar x) = Unit
WriteResponses .opened closeWrite = Unit 

writeNext : (j : WriteState) (c : WriteCommand j) → WriteResponses j c → WriteState
writeNext .opened (writeChar x) unit = opened
writeNext .opened closeWrite unit = closed
writeNext .closed (openWrite fileName) opened = opened
writeNext .closed (openWrite fileName) closed = closed

WRITE : WriteState ▸ WriteState
WRITE = record { Cmd = WriteCommand ; Resp = WriteResponses ; next = writeNext }


data ReadState : Set where
  opened : (eof : Bool) → ReadState
  closed : ReadState


data ReadCommand : ReadState → Set where
  -- can only open a closed filed
  openRead : String -> ReadCommand closed

  -- can only read char when not EOF
  readChar : ReadCommand (opened tt)

  -- can close an opened file, regardless of EOF
  closeRead : ∀ {b} → ReadCommand (opened b)


ReadResponses : (j : ReadState) → ReadCommand j → Set
ReadResponses .closed (openRead x) =  ReadState
ReadResponses .(opened tt) (readChar) = Char × Bool
ReadResponses .(opened _) closeRead = Unit

readNext : (j : ReadState)(c : ReadCommand j) → ReadResponses j c → ReadState
readNext .closed (openRead x) (opened tt) = opened tt
readNext .closed (openRead x) (opened ff) = opened ff
readNext .closed (openRead x) closed = closed
readNext .(opened tt) readChar (x , eof) = opened eof
readNext .(opened _) closeRead unit = closed


READ : ReadState ▸ ReadState
READ = record { Cmd = ReadCommand ; Resp = ReadResponses ; next = readNext }




{- Connor : I'm building the next bit for you.
   When things go wrong, we need to trigger an error condition and abort
   mission. However, if we have other stuff going on (open files, etc),
   it may not always be ok to drop everything and run away. There will
   be some states in which it is safe to escape (and deliver a suitable
   error message, perhaps) and other states in which escape should be
   impossible.
   If it is safe to issue an error message, we should be able to do so
   without fear of any response from the environment that would oblige
   us to carry on.
-}


-- ErrorC :  Pow I → Pow I
data ErrorC {I : Set}(SafeMessage : Pow I)(i : I) : Set where
  error : SafeMessage i -> ErrorC SafeMessage i
    -- the SafeMessage parameter tells us what is an acceptable
    -- error message in any given state; in states where this gives
    -- Zero, it will be impossible to trigger an error!

ErrorR : {I : Set}{SafeMessage : I -> Set}(i : I)(c : ErrorC SafeMessage i) -> Set
ErrorR _ _ = ⊥  -- there's no comeback

errorNext : {I : Set}{SafeMessage : I -> Set}
            (i : I)(c : ErrorC SafeMessage i) -> ErrorR i c -> I
errorNext i c ()  -- so we don't have to say how the state will evolve

ERROR : {I : Set}(SafeMessage : I -> Set) -> I ▸ I
ERROR SafeMessage = record { Cmd = ErrorC SafeMessage ; Resp = ErrorR ; next = errorNext }  



ERROR2 : {I : Set}(SafeMessage : Pow I) → I ▸ I
ERROR2 SafeMessage = {!!}

CPState : Set
CPState =  (ReadState × WriteState)


data ReadError : Pow ReadState where
  couldNotOpenFile : ReadError closed

data WriteError : Pow WriteState where
  couldNotOpenFile : WriteError closed


COPY : CPState ▸ CPState
COPY2 : CPState ▸ CPState

COPY = ((READ ⊔ ERROR ReadError) ⊗ (WRITE ⊔ ERROR WriteError))
COPY2 = (READ ⊗ WRITE ) ⊔ ERROR \ { (f , s) -> ReadError f + WriteError s}

FinalState : Pow CPState
FinalState (closed , closed) = Unit
FinalState _ =  ⊥
