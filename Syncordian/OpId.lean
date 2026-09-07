namespace Syncordian

variable
  ( Peer
  : Type)

-- The sole namespace of operation identifiers.  An acknowledgement is
-- idempotent and deliberately has no `OpId`.
structure OpId
    where
  writer   : Peer
  sequence : Nat
deriving DecidableEq, Repr


end Syncordian
