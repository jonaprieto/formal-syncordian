import Syncordian.Line

namespace Syncordian

variable (
    Position
    Content
    Peer
    : Type)

variable
  [LT Peer]

structure Document
    where
  lines : List (Line Position Content Peer)

variable {Position Content Peer}

-- No two lines in a document share an identity.
def Document.HasUniqueIds
    (doc : Document Position Content Peer)
    : Prop :=
  ∀ ⦃a b⦄,
    a ∈ doc.lines →
    b ∈ doc.lines →
    a.id = b.id →
    a = b

variable [spec : PositionSpec Position]

def Document.HasPresentParents
    (doc : Document Position Content Peer)
    : Prop :=
  ∀ line, line ∈ doc.lines →
    line.isBoundary ∨
      ((∃ parent ∈ doc.lines, parent.id = line.fixed.parentLeft) ∧
        ∃ parent ∈ doc.lines, parent.id = line.fixed.parentRight)

def Document.HasParentIntervals
    (doc : Document Position Content Peer)
    : Prop :=
  ∀ line, line ∈ doc.lines →
    line.isBoundary ∨
      ∀ left right,
        left ∈ doc.lines →
        left.id = line.fixed.parentLeft →
        right ∈ doc.lines →
        right.id = line.fixed.parentRight →
        left.position < line.position ∧
          line.position < right.position

def Document.HasSortedLines
    (doc : Document Position Content Peer)
    : Prop :=
  Line.Sorted doc.lines

def Document.HasBottom
    (doc : Document Position Content Peer)
    : Prop :=
  ∃ line ∈ doc.lines, line.isBottom

def Document.HasTop
    (doc : Document Position Content Peer)
    : Prop :=
  ∃ line ∈ doc.lines, line.isTop

structure Document.WellFormed
    (doc : Document Position Content Peer)
    : Prop where
  bottom          : Document.HasBottom doc
  top             : Document.HasTop doc
  uniqueIds       : Document.HasUniqueIds doc
  presentParents  : Document.HasPresentParents doc
  parentIntervals : Document.HasParentIntervals doc
  sortedLines     : Document.HasSortedLines doc

-- subtype, a document + what it means to be well-defined/formed.
abbrev WellFormedDocument
    ( Position
      Content
      Peer
      : Type)
    [PositionSpec Position]
    [LT Peer]
    :=
  { doc : Document Position Content Peer // Document.WellFormed doc }

theorem WellFormedDocument.bottom_unique
    (doc : WellFormedDocument Position Content Peer)
    {a b : Line Position Content Peer}
    (ha : a ∈ doc.val.lines)
    (hb : b ∈ doc.val.lines)
    (ha_id : a.id = LineId.bottom)
    (hb_id : b.id = LineId.bottom)
    : a = b :=
  doc.property.uniqueIds ha hb (ha_id.trans hb_id.symm)

theorem WellFormedDocument.top_unique
    (doc : WellFormedDocument Position Content Peer)
    {a b : Line Position Content Peer}
    (ha : a ∈ doc.val.lines)
    (hb : b ∈ doc.val.lines)
    (ha_id : a.id = LineId.top)
    (hb_id : b.id = LineId.top)
    : a = b :=
  doc.property.uniqueIds ha hb (ha_id.trans hb_id.symm)

variable [DecidableEq Peer]

def WellFormedDocument.visibleLines
    (doc : WellFormedDocument Position Content Peer)
    : List (Line Position Content Peer) :=
  doc.val.lines.filter fun line => decide line.isVisible

def WellFormedDocument.read
    (doc : WellFormedDocument Position Content Peer)
    : List Content :=
  doc.visibleLines.map (·.fixed.content)

end Syncordian
