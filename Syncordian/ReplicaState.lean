import Syncordian.Document
import Syncordian.Message
import Syncordian.Operation


namespace Syncordian

variable
  (
    Position
    Content
    Peer
    Tag
    : Type
  )

variable [PositionSpec Position] [LT Peer] [DecidableEq Peer]

structure ReplicaState  where
  document   : Document Position Content Peer
  progress   : Peer → Nat -- progress vector
  -- Received messages that are not yet deliverable, at most one per operation
  -- identifier.
  buffer     : List (Message Position Content Peer Tag)
  operations : List (Operation Position Content Peer Tag) -- applied operations
  aliases    : LineId Peer → Option (LineId Peer)


def initialState : ReplicaState Position Content Peer Tag :=
  {
    document := Document.empty
    progress := fun _ => 0
    buffer := []
    operations := []
    aliases := fun _ => none
  }

instance
    : Inhabited (ReplicaState Position Content Peer Tag) :=
  ⟨initialState Position Content Peer Tag⟩


end Syncordian
