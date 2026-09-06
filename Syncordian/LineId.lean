import Syncordian.OperationId

namespace Syncordian

variable (
    Peer
    : Type)
variable [LT Peer]

inductive LineId
    where
  | bottom
  | operation (id : OpId Peer)
  | top
deriving DecidableEq, Repr

def LineId.lt
    : LineId Peer → LineId Peer → Prop
  | .bottom, .bottom => False
  | .bottom, .top => True
  | .bottom, .operation _ => True
  | .operation _, .bottom => False
  | .operation _, .top => True
  | .operation a, .operation b =>
      a.writer < b.writer ∨ (a.writer = b.writer ∧ a.sequence < b.sequence)
  | .top, .bottom => False
  | .top, .top => False
  | .top, .operation _ => False

instance instLTLineId
    : LT (LineId Peer) where
  lt := LineId.lt Peer

variable {Peer}

instance instDecidableLTLineId
    [DecidableEq Peer]
    [DecidableLT Peer]
    (a b : LineId Peer)
    : Decidable (a < b) := by
  cases a <;> cases b <;> unfold LT.lt instLTLineId LineId.lt <;> infer_instance

end Syncordian
