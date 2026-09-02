import Syncordian.Position
import Syncordian.Status

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

-- the pair of parent lines that defines the interval where a block began.
-- The session identifies the authored block.
structure Session (Peer : Type) where
  left : LineId Peer
  right : LineId Peer
deriving DecidableEq, Repr


-- Write-once protocol data.
structure LineFixed
  ( Position
    Content
    Peer
    : Type)
  where
  id : LineId Peer -- identity of the line
  position : Position
  parentLeft : LineId Peer
  parentRight : LineId Peer
  session : Session Peer -- Is a better name for "Session"?
  content : Content
  writer : Peer

-- Things unsolved to figure with M and N
-- insertion_attempts: integer(),
--  commit_at: Syncordian.Basic_Types.commit_list(),
--  op_id: Syncordian.Basic_Types.op_id() | nil,
-- signature: Syncordian.Basic_Types.signature(),

-- The evolving data of a line.
structure LineState (Peer : Type)
  where
  status : Status
  -- ponytail: List-backed response set; use a finite set when acknowledgements are modeled.
  responses : List Peer

structure Line
  ( Position
    Content
    Peer
    : Type)
    where
  fixed : LineFixed Position Content Peer
  state : LineState Peer

-- A transition can only update the state; `fixed` is carried forward unchanged.
def Line.setStatus {Position Content Peer : Type}
    (line : Line Position Content Peer)
    (next : Status)
    -- prop. obligation:
    (_ : line.state.status.canBecome next) :
    Line Position Content Peer :=
  { line with state := {
    line.state with status := next
    }
  }

-- only changes the state no the fixed data
theorem Line.setStatus_fixed {Position Content Peer : Type}
    (line : Line Position Content Peer)
    (next : Status)
    (h : line.state.status.canBecome next) :
    (line.setStatus next h).fixed = line.fixed := by
  rfl

-- same for responses, nothing changes.
theorem Line.setStatus_responses {Position Content Peer : Type}
    (line : Line Position Content Peer)
    (next : Status)
    (h : line.state.status.canBecome next) :
    (line.setStatus next h).state.responses = line.state.responses := by
  rfl



end Syncordian
