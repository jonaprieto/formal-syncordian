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

def LineId.lt [LT Peer] : LineId Peer → LineId Peer → Prop
  --
  | .bottom, .bottom => False
  | .bottom, .top => True
  | .bottom, .operation _ => True
  ---
  | .top, .bottom => False
  | .top, .top => False
  | .top, .operation _ => True
  --
  | .operation _, .bottom => False
  | .operation _, .top => False
  | .operation a, .operation b =>
      a.writer < b.writer ∨
      ( a.writer = b.writer ∧
       a.sequence < b.sequence
      )

instance instLTLineId [LT Peer] : LT (LineId Peer) where
  lt := LineId.lt

instance instDecidableLtLineId [LT Peer] [DecidableEq Peer] [DecidableLT Peer]
    (a b : LineId Peer) : Decidable (a < b) := by
  cases a <;> cases b <;>
    (show Decidable (LineId.lt _ _); unfold LineId.lt; infer_instance)

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
  position : Position -- where the line sits
  parentLeft : LineId Peer
  parentRight : LineId Peer
  session : Session Peer -- Is there a better name for "Session"?
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
  responses : List Peer -- which peers have acknowledged the line

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

abbrev Line.isBottomSentinel (line : Line Position Content Peer) : Prop :=
  line.fixed.id = LineId.bottom

abbrev Line.isTopSentinel (line : Line Position Content Peer) : Prop :=
  line.fixed.id = LineId.top

abbrev Line.isBoundary (line : Line Position Content Peer) : Prop :=
  line.isBottomSentinel ∨ line.isTopSentinel

abbrev Line.isBottom (line : Line Position Content Peer)
  [spec : PositionSpec Position] : Prop :=
  line.isBottomSentinel ∧ line.position = spec.bottom

abbrev Line.isTop (line : Line Position Content Peer)
  [spec : PositionSpec Position] : Prop :=
  line.isTopSentinel ∧ line.position = spec.top

def Line.lt [PositionSpec Position] [LT Peer]
    (a b : Line Position Content Peer) : Prop :=
  a.position < b.position ∨ (a.position = b.position ∧ a.id < b.id)

instance instLTLine [PositionSpec Position] [LT Peer] :
    LT (Line Position Content Peer) where
  lt := Line.lt

def Line.Sorted [PositionSpec Position] [LT Peer] :
    List (Line Position Content Peer) → Prop
  | a :: b :: rest => a < b ∧ Line.Sorted (b :: rest)
  | _ => True

instance instDecidableLtLine [PositionSpec Position] [LT Peer] [DecidableEq Peer]
    [DecidableLT Peer] [DecidableEq Position]
    [∀ a b : Position, Decidable (a < b)]
    (a b : Line Position Content Peer) : Decidable (a < b) := by
  show Decidable (Line.lt a b)
  unfold Line.lt; infer_instance

instance instDecidableLineSorted [PositionSpec Position] [LT Peer] [DecidableEq Peer]
    [DecidableLT Peer] [DecidableEq Position]
    [∀ a b : Position, Decidable (a < b)] :
    (l : List (Line Position Content Peer)) → Decidable (Line.Sorted l)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | a :: b :: rest =>
    have : Decidable (Line.Sorted (b :: rest)) := instDecidableLineSorted (b :: rest)
    by unfold Line.Sorted; infer_instance

-- A transition can only update the state; `fixed` is carried forward unchanged.
def Line.setStatus
    (line : Line Position Content Peer)
    (next : Status)
    -- prop. obligation:
    (_ : line.status.canBecome next) :
    Line Position Content Peer :=
  { line with state := {
    line.state with status := next
    }
  }

-- only changes the state no the fixed data
theorem Line.setStatus_fixed
    (line : Line Position Content Peer)
    (next : Status)
    (h : line.status.canBecome next) :
    (line.setStatus next h).fixed = line.fixed := by
  rfl

-- same for responses, nothing changes.
theorem Line.setStatus_responses
    (line : Line Position Content Peer)
    (next : Status)
    (h : line.status.canBecome next) :
    (line.setStatus next h).state.responses = line.state.responses := by
  rfl


end Syncordian
