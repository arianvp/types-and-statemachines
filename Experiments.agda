module Experiments where
open import Prelude
open import InteractionStructures


data WriteState : Set where
  opened closed : WriteState

data WriteCommand : WriteState → Set where
  openWrite  : (fileName : String) → WriteCommand closed
  writeChar  : Char                → WriteCommand opened
  closeWrite :                       WriteCommand opened

WriteResponse : (j : WriteState) (c : WriteCommand j) → Set
WriteResponse .closed (openWrite fileName) = WriteState
WriteResponse .opened (writeChar x) = Unit
WriteResponse .opened closeWrite = Unit

writeNext : (j : WriteState) (c : WriteCommand j) → WriteResponse j c → WriteState
writeNext .closed (openWrite fileName) r = opened
writeNext .opened (writeChar x) r = opened
writeNext .opened closeWrite r = closed

WRITE : WriteState ▸ WriteState
WRITE = record { Cmd = WriteCommand ; Resp = WriteResponse ; next = writeNext }

data ReadState : Set where
  opened : (eof : Bool) → ReadState
  closed : ReadState

data ReadCommand : ReadState → Set where
  openRead : (fileName : String) → ReadCommand closed
  -- we can only read if we're not at EOF
  readChar : ReadCommand (opened tt)
  closeRead : {eof : Bool} → ReadCommand (opened eof)


ReadResponse : (j : ReadState) (c : ReadCommand j) → Set
ReadResponse .closed (openRead fileName) = Bool
ReadResponse .(opened tt) readChar = Maybe Char
ReadResponse .(opened _) closeRead = Unit

readNext : (j : ReadState) (c : ReadCommand j) → ReadResponse j c → ReadState
readNext .closed (openRead fileName) eof = opened eof
readNext .(opened tt) readChar Nothing =  opened tt
readNext .(opened tt) readChar (Just x) = opened ff
readNext .(opened _) closeRead r = closed 

READ : ReadState ▸ ReadState
READ = record { Cmd = ReadCommand ; Resp = ReadResponse ; next = readNext }

-- Now we want to combine READ and WRITE for a CP interface


{-
openFile : Free○ FILES  (λ x → Unit) FileClosed
openFile = {!!}  -- step (OpenFile , (λ { t → stop unit ; f → stop  unit }))

readFile : Free○ FILES (λ x → Maybe Char) FileOpened
readFile = step (ReadFile , (λ y →  stop y))

closeFile : Free○ FILES (λ x → Unit) FileOpened
closeFile = step (CloseFile , (λ y → stop y) )


operations : Free○ FILES (λ x → Char) FileClosed
operations = openFile >>= λ { unit → {!!}} 
  where
    open IxMonad (free○-IxMonad FILES)
-}


data ResponseState : Set where
  StatusLineOpen HeadersOpen BodyOpen ResponseEnded : ResponseState
  

data Status : Set where
  Ok : Status
  NotFound : Status
  Unauthorized : Status

data Header : Set where
  WWWAuthenticate : String → Header
  
postulate Request : Set

data ResponseCommand : ResponseState → Set where
  WriteStatus : Status → ResponseCommand StatusLineOpen
  WriteHeader : Header → ResponseCommand HeadersOpen
  CloseHeaders : ResponseCommand HeadersOpen
  Send : (body : String) → ResponseCommand BodyOpen
  End : ResponseCommand BodyOpen
  -- some commands can always be executed

  GetRequestContext : {x : ResponseState} → ResponseCommand x


ResponseResponse : (i : ResponseState) (j : ResponseCommand i) → Set
ResponseResponse .StatusLineOpen (WriteStatus x) = Unit
ResponseResponse .HeadersOpen (WriteHeader x) = Unit
ResponseResponse .HeadersOpen CloseHeaders = Unit
ResponseResponse .BodyOpen (Send body) = Unit
ResponseResponse .BodyOpen End = Unit
ResponseResponse _         GetRequestContext = Request

ResponseNext : (i : ResponseState) (j : ResponseCommand i) → ResponseResponse i j → ResponseState
ResponseNext .StatusLineOpen (WriteStatus x) x₁ = HeadersOpen
ResponseNext .HeadersOpen (WriteHeader x) x₁ = HeadersOpen
ResponseNext .HeadersOpen CloseHeaders x = BodyOpen
ResponseNext .BodyOpen (Send body) x = BodyOpen
ResponseNext .BodyOpen End x =  ResponseEnded 
ResponseNext y   ReadBody x = y


RESPONSE : ResponseState ▸ ResponseState
RESPONSE = record { Cmd = ResponseCommand ; Resp = ResponseResponse ; next = ResponseNext }

-- named after Robert Atkey
data AtKey {I : Set} ( X : Set) ( i : I) : I → Set where
  at : X → AtKey X i i


ipure : {S : Set} → {T : S ▸ S} {X : Set} {s : S} → (x : X) → Free○ T (AtKey X s) s
ipure x = stop (at x)

writeStatus : Status → Free○ RESPONSE (AtKey Unit HeadersOpen) StatusLineOpen
writeStatus x = step ((WriteStatus x) , ipure)

writeHeader : Header → Free○ RESPONSE  (AtKey Unit HeadersOpen) HeadersOpen
writeHeader x = step (WriteHeader x ,  ipure)

closeHeaders : Free○ RESPONSE (AtKey Unit BodyOpen) HeadersOpen
closeHeaders = step ( CloseHeaders , ipure) 


writeHeaders : Header → Free○ RESPONSE (AtKey Unit BodyOpen) HeadersOpen
writeHeaders x = writeHeader x >>= ( λ { (at x₁) → closeHeaders }) 
  where open IxMonad (free○-IxMonad RESPONSE)

send : String → Free○ RESPONSE (AtKey Unit BodyOpen) BodyOpen
send x = step (Send x , ipure)

end : Free○ RESPONSE (AtKey Unit ResponseEnded) BodyOpen
end = step (End , ipure)

-- in any state, we can read the request context
getRequestContext : ∀ {k} → Free○ RESPONSE (AtKey Request k) k
getRequestContext = step (GetRequestContext , ipure)

respond : (body : String) → Free○ RESPONSE (AtKey Unit ResponseEnded) BodyOpen
respond body = send body >>= λ { (at x) → end }
  where open IxMonad (free○-IxMonad RESPONSE)

-- what do we get if we take the sum of two http servers?
-- we either handle t
test : Free○ (RESPONSE ⊔ RESPONSE) (AtKey Unit ResponseEnded) StatusLineOpen
test =   {!!}


-- what does it mean to take the product of two http servers?
-- if we get two flows, we must complete both flows ... intersting
-- i'm not yet sure how this is useful
test2 : Free○ (RESPONSE ⊓ RESPONSE) (AtKey Unit ResponseEnded) StatusLineOpen
test2 = step ((GetRequestContext , GetRequestContext) , (λ { (inl x) → {!!} ; (inr x) → {!!}}))

-- Perhaps we could use this to look at the context, and choose if we do HTTP1 or HTTP2 ?
postulate HTTP1 HTTP2 : ResponseState ▸ ResponseState
httpserver : Free○ (HTTP1 ⊔ HTTP2) (AtKey Unit ResponseEnded) StatusLineOpen
httpserver = step {!!}



-- a server goes through the entire Webmachine statemachine
Server :  (X : Set) → Set
Server X =  Free○ RESPONSE (AtKey X ResponseEnded) StatusLineOpen


-- denyAccess spits out unauthorized and aborts the request
denyAccess : Free○ RESPONSE (AtKey Unit ResponseEnded) StatusLineOpen
denyAccess  =
  writeStatus  Unauthorized >>= λ { (at x) →
  writeHeader (WWWAuthenticate "realm arian") >>= λ { (at x₁) →
  closeHeaders >>= λ { (at x₂) → end}}} 
  where open IxMonad (free○-IxMonad RESPONSE)


if_then_else : {A : Set} (b : Bool) → A → A → A
if tt then y else z = y
if ff then y else z = z

postulate urlIsAllowed : Request → Bool

server : Server Unit
server =
  getRequestContext >>= (λ { (at request) →
  if urlIsAllowed request
  then
    writeStatus Ok >>= (λ { (at x) →
     closeHeaders >>= (λ { (at x₁) →
     respond "welcome to my server" }) })
  else
    denyAccess})
  where open IxMonad (free○-IxMonad RESPONSE)






    
data HaskellIOCommand : Set where
  putStrLn : String → HaskellIOCommand
  readLine : HaskellIOCommand

HaskellIOResponse : HaskellIOCommand → Set
HaskellIOResponse (putStrLn x) = Unit
HaskellIOResponse readLine = String


HASKELLIO : Unit ▸ Unit
HASKELLIO = record { Cmd =  λ x → HaskellIOCommand ; Resp = λ x → HaskellIOResponse ; next = λ a b c → unit }



-- Server X =  Free○ RESPONSE (AtKey X ResponseEnded) StatusLineOpen
runServer : ∀ {X} → Free○ RESPONSE (AtKey X ResponseEnded)  StatusLineOpen  → Free○ HASKELLIO (λ x → X) unit
runServer (stop ())
runServer (step (WriteStatus x , snd₁)) = step {!!}
runServer (step (GetRequestContext , snd₁)) = step {!!}




-- Hypermedia as the Engine of Application State

data Path (i o : Set) : Set where
  

