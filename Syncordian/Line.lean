import Syncordian.Position
import Syncordian.Status
import Syncordian.LineId
import Syncordian.Session

namespace Syncordian

variable (
    Position
    Content
    Peer
    : Type)

-- Write-once protocol data.
structure LineFixed
    where
  id          : LineId Peer -- identity of the line
  position    : Position
  parentLeft  : LineId Peer
  parentRight : LineId Peer
  session     : Session Peer -- Is a better name for "Session"?
  content     : Content
  writer      : Peer

-- Things unsolved to figure with M and N
-- insertion_attempts: integer(),
--  commit_at: Syncordian.Basic_Types.commit_list(),
--  op_id: Syncordian.Basic_Types.op_id() | nil,
-- signature: Syncordian.Basic_Types.signature(),

-- The evolving data of a line.
structure LineState
    where
  status    : Status
  responses : List Peer

structure Line
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
    (line : Line Position Content Peer)
    : Prop :=
  line.fixed.id = LineId.bottom

abbrev Line.isTopSentinel
    (line : Line Position Content Peer)
    : Prop :=
  line.fixed.id = LineId.top

abbrev Line.isBoundary
    (line : Line Position Content Peer)
    : Prop :=
  line.isBottomSentinel ∨ line.isTopSentinel

abbrev Line.isBottom
    (line : Line Position Content Peer)
    [spec : PositionSpec Position]
    : Prop :=
  line.isBottomSentinel ∧ line.position = spec.bottom

abbrev Line.isTop
    (line : Line Position Content Peer)
    [spec : PositionSpec Position]
    : Prop :=
  line.isTopSentinel ∧ line.position = spec.top

def Line.lt
    [PositionSpec Position]
    [LT Peer]
    (a b : Line Position Content Peer)
    : Prop :=
  a.position < b.position ∨ (a.position = b.position ∧ a.id < b.id)

instance instLTLine
    [PositionSpec Position]
    [LT Peer]
    : LT (Line Position Content Peer) where
  lt := Line.lt

def Line.Sorted
    [PositionSpec Position]
    [LT Peer]
    : List (Line Position Content Peer) → Prop
  | a :: b :: rest => a < b ∧ Line.Sorted (b :: rest)
  | _ => True

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

end Syncordian
