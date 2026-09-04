
namespace Syncordian

variable (
    Peer
    : Type)
variable [LT Peer]

structure OpId
    where
  writer   : Peer
  sequence : Nat
deriving DecidableEq, Repr

inductive LineId
    where
  | operation (id : OpId Peer)
  | bottom
  | top
deriving DecidableEq, Repr

def LineId.lt
    : LineId Peer → LineId Peer → Prop
  | .bottom, .bottom => False
  | .bottom, .top => True
  | .bottom, .operation _ => True
  | .top, .bottom => False
  | .top, .top => False
  | .top, .operation _ => False
  | .operation _, .bottom => False
  | .operation _, .top => True
  | .operation a, .operation b =>
      a.writer < b.writer ∨ (a.writer = b.writer ∧ a.sequence < b.sequence)

instance instLTLineId
    : LT (LineId Peer) where
  lt := LineId.lt Peer

end Syncordian
