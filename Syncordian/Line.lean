import Syncordian.Position
import Syncordian.Status
import Syncordian.LineId
import Syncordian.Session

namespace Syncordian

variable
  (
    Position
    Content
    Peer
    : Type
  )

section NormalLine

-- Write-once protocol data.
structure LineFixedData
    where
  id          : OpId Peer -- identity of the line; only an insert can create one
  position    : Position
  parentLeft  : LineId Peer
  parentRight : LineId Peer
  session     : Session Peer -- Is a better name for "Session"?
  content     : Content

-- Things unsolved to figure with M and N
-- insertion_attempts: integer(),
--  commit_at: Syncordian.Basic_Types.commit_list(),
--  op_id: Syncordian.Basic_Types.op_id() | nil,
-- signature: Syncordian.Basic_Types.signature(),

-- The evolving data of a line.
structure LineStateData
    where
  status    : Status
  responses : List Peer

structure NormalLine
    where
  fixed : LineFixedData Position Content Peer
  state : LineStateData Peer

abbrev NormalLine.id
    (line : NormalLine Position Content Peer)
    : OpId Peer :=
  line.fixed.id

abbrev NormalLine.position
    (line : NormalLine Position Content Peer)
    : Position :=
  line.fixed.position

abbrev NormalLine.parentLeft
    (line : NormalLine Position Content Peer)
    : LineId Peer :=
  line.fixed.parentLeft

abbrev NormalLine.parentRight
    (line : NormalLine Position Content Peer)
    : LineId Peer :=
  line.fixed.parentRight

abbrev NormalLine.status
    (line : NormalLine Position Content Peer)
    : Status :=
  line.state.status

abbrev NormalLine.author
    (line : NormalLine Position Content Peer)
    : Peer :=
  line.id.writer

def setStatus
    (line : NormalLine Position Content Peer)
    (next : Status)
    (_ : line.state.status.canBecome next)
    : NormalLine Position Content Peer :=
  { line with state := { line.state with status := next } }

end NormalLine

inductive Line where
  | bottom
  | normal (line : NormalLine Position Content Peer)
  | top

variable {Position Content Peer}

abbrev Line.id
    : (line : Line Position Content Peer) →  LineId Peer
  | .bottom  => .bottom
  | .top     => .top
  | .normal line => .operation line.fixed.id

abbrev Line.position
    [spec : PositionSpec Position]
    : (line : Line Position Content Peer) → Position
  | .bottom  => spec.bottom
  | .top     => spec.top
  | .normal line => line.fixed.position

def Line.parents?
  : Line Position Content Peer → Option (LineId Peer × LineId Peer)
  | .bottom | .top => none
  | .normal line   => some (line.parentLeft, line.parentRight)

abbrev Line.status
  : (line : Line Position Content Peer) → Status
  | .bottom | .top  => .settled
  | .normal line  => line.state.status

abbrev Line.isBoundary
    : Line Position Content Peer → Prop
  | .bottom | .top  => True
  | .normal _       => False

abbrev Line.isBottom
    : (line : Line Position Content Peer) →  Prop
  | .bottom => True
  | _       => False

abbrev Line.isTopSentinel
    : (line : Line Position Content Peer) →  Prop
  | .top => True
  | _ => False

def Line.lt
    [PositionSpec Position]
    [LT Peer]
    (a b : Line Position Content Peer)
    : Prop :=
  a.position < b.position ∨
    (a.position = b.position ∧ a.id < b.id)

instance instLTLine
    [PositionSpec Position]
    [LT Peer]
    : LT (Line Position Content Peer) where
  lt := Line.lt

instance instDecidableLTLine
    [PositionSpec Position]
    [DecidableEq Position]
    [DecidableLT Position]
    [LT Peer]
    [DecidableEq Peer]
    [DecidableLT Peer]
    (a b : Line Position Content Peer)
    : Decidable (a < b) :=
  inferInstanceAs (Decidable (_ ∨ _))

def Line.Sorted
    [PositionSpec Position]
    [LT Peer]
    : List (Line Position Content Peer) → Prop
  | a :: b :: rest => a < b ∧ Line.Sorted (b :: rest)
  | _ => True

def Line.isVisible
    : Line Position Content Peer → Prop
  | .bottom | .top => False
  | .normal line   => line.state.status ≠ .tombstone

instance instDecidableLineVisible
    (line : Line Position Content Peer)
    : Decidable line.isVisible :=
  match line with
  | .bottom | .top => isFalse id
  | .normal l      => inferInstanceAs (Decidable (l.state.status ≠ .tombstone))

end Syncordian
