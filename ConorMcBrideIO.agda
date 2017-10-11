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




