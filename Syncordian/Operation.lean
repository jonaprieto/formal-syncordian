import Syncordian.OpId
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
      (wireTag : Tag)

  | delete
      (id : OpId Peer)
      (target : LineId Peer)
      (wireTag : Tag)

  -- Acknowledgements are idempotent response updates, so they have no `OpId`.
  | acknowledge
      (target : LineId Peer)
      (peer : Peer)
      (wireTag : Tag)

deriving DecidableEq, Repr

variable {Position Content Peer Tag}

def Operation.wireTag
    : Operation Position Content Peer Tag → Tag
  | .insert _ _ _ _ _ _ _ tag   => tag
  | .delete _ _ tag             => tag
  | .acknowledge _ _ tag        => tag

def Operation.author
    : Operation Position Content Peer Tag → Peer
  | .insert id _ _ _ _ _ _ _  => id.writer   -- who creates the line
  | .delete id _ _             => id.writer  -- who deletes the line
  | .acknowledge _ peer _        => peer     -- who confirmed the reception


end Syncordian
