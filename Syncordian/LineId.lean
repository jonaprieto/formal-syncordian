
namespace Syncordian

structure OpId (Peer : Type) where
  writer : Peer
  sequence : Nat
deriving DecidableEq, Repr

inductive LineId (Peer : Type) where
  | operation (id : OpId Peer)
  | bottom
  | top
deriving DecidableEq, Repr

def LineId.lt
    [LT Peer]
    : LineId Peer → LineId Peer → Prop
  | .bottom, .bottom => False
  | .bottom, .top => True
  | .bottom, .operation _ => True
  | .top, .bottom => False
  | .top, .top => False
  | .top, .operation _ => True
  | .operation _, .bottom => False
  | .operation _, .top => False
  | .operation a, .operation b =>
      a.writer < b.writer ∨ (a.writer = b.writer ∧ a.sequence < b.sequence)

instance instLTLineId
    [LT Peer]
    : LT (LineId Peer) where
  lt := LineId.lt

end Syncordian
