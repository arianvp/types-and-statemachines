module TCP where
open import Prelude
open import InteractionStructures
 

data State : Set where
  Closed Listen SynReceived SynSent Established FinWait1 FinWait2 Closing TimeWait CloseWait Lastack : State


record Flags : Set where
  constructor MkFlags
  field
    LISTEN : Bool
    CLOSE : Bool
    SEND : Bool
    TIMEOUT : Bool
    NS : Bool
    CWR : Bool
    ECE : Bool
    URG : Bool
    ACK : Bool
    PSH : Bool
    RST : Bool
    SYN : Bool
    FIN : Bool

    
  
cmd :  Flags → Pow State
cmd x x₁ = {!x!}
  

TCP : State ▸ State
TCP = record { Cmd = {!!} ; Resp = {!!} ; next = {!!} }


