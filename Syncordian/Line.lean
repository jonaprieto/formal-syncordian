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
structure LineState
    (Peer : Type)
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

variable {Position Content Peer : Type}

-- Shorthands for the fields callers reach for most. `abbrev`, so they stay
-- definitionally the underlying projection and proofs by `rfl` keep working.
abbrev Line.id (line : Line Position Content Peer) : LineId Peer := line.fixed.id
abbrev Line.position (line : Line Position Content Peer) : Position := line.fixed.position
abbrev Line.status (line : Line Position Content Peer) : Status := line.state.status

abbrev Line.isBottomSentinel
    {Peer}
    (line : Line Position Content Peer) :=
  line.fixed.id = LineId.bottom

abbrev Line.isBottom
    {Peer}
    (line : Line Position Content Peer)
    [spec : PositionSpec Position]
    : Prop :=
  line.isBottomSentinel ∧ line.position = spec.bottom

abbrev Line.isTopSentinel
    {Peer}
    (line : Line Position Content Peer) :=
  line.fixed.id = LineId.top

abbrev Line.isTop
    {Peer}
    (line : Line Position Content Peer)
    [spec : PositionSpec Position]
    : Prop :=
  line.isTopSentinel ∧ line.position = spec.top

abbrev Line.isBoundary
    (line : Line Position Content Peer)
    [spec : PositionSpec Position]
    : Prop :=
  line.isBottom ∨ line.isTop

-- A transition can only update the state; `fixed` is carried forward unchanged.
def Line.setStatus
    (line : Line Position Content Peer)
    (next : Status)
    -- prop. obligation:
    (_ : line.status.canBecome next)
    : Line Position Content Peer :=
  { line with state := {
    line.state with status := next
    }
  }

-- only changes the state no the fixed data
theorem Line.setStatus_fixed
    (line : Line Position Content Peer)
    (next : Status)
    (h : line.status.canBecome next)
    : (line.setStatus next h).fixed = line.fixed := by
  rfl

-- same for responses, nothing changes.
theorem Line.setStatus_responses
    (line : Line Position Content Peer)
    (next : Status)
    (h : line.status.canBecome next)
    : (line.setStatus next h).state.responses = line.state.responses := by
  rfl


end Syncordian
