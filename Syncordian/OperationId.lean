namespace Syncordian

variable
  ( Peer
  : Type)

structure OpId
    where
  writer   : Peer
  sequence : Nat
deriving DecidableEq, Repr


end Syncordian
