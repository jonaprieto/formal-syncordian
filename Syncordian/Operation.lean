import Syncordian.OperationId
import Syncordian.LineId


namespace Syncordian

variable
  (
    Position
    Content
    Peer
    Tag
    : Type
  )


inductive Operation
    where
  | insert
      (id : OpId Peer)
      (rank : Nat)
      (position : Position)
      (parentLeft parentRight : LineId Peer)
      (supersedes : Option (LineId Peer))
      (content : Content)
      (writer : Peer)
      (tag : Tag)

  | delete
      (id : OpId Peer)
      (target : LineId Peer)
      (tag : Tag)

  | acknowledge
      (id : OpId Peer)
      (target : LineId Peer)
      (peer : Peer)
      (tag : Tag)
deriving DecidableEq, Repr

end Syncordian
