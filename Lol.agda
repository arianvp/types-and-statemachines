open import Data.Product
open import Data.Unit
open import Relation.Unary
open import Category.Monad.Predicate
open import Data.Container.Indexed
open import Data.Container.Indexed.Combinator
open import Data.Container.Indexed.FreeMonad

data DoorState : Set where
  DoorOpened DoorClosed : DoorState

data DoorCmd :  DoorState → Set where
  Open : DoorCmd DoorClosed
  Close : DoorCmd DoorOpened
  RingBell : DoorCmd DoorClosed

data DoorResult : Set where
  Jammed OK : DoorResult


DoorResp : {s : DoorState} → DoorCmd s → Set
DoorResp Open = DoorResult
DoorResp Close =  ⊤
DoorResp RingBell = ⊤

doorNext : {s : DoorState} (c : DoorCmd s) → DoorResp c → DoorState
doorNext Open Jammed = DoorClosed
doorNext Open OK = DoorOpened
doorNext Close unit = DoorClosed
doorNext RingBell unit = DoorClosed


DOOR : DoorState ▷ DoorState
DOOR = DoorCmd ◃ DoorResp / doorNext

leaf2 :  ⟦ ?  ⟧ ?
leaf2 = leaf 
  where
  open RawPMonad (rawPMonad {C = DOOR})

{- ringBell : {!⟦ DOOR ⟧ (DOOR ⋆ ?) ⊆ DOOR ⋆ ?!}
ringBell = do ({!!} , {!!})
  where
  open RawPMonad (rawPMonad {C = DOOR})
-}
