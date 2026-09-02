import Syncordian.Line

namespace Syncordian

variable (Position Content Peer : Type)

structure Document where
  lines : List (Line Position Content Peer)

variable {Position Content Peer}

-- No two lines in a document share an identity.
def has_unique_ids (doc : Document Position Content Peer) : Prop :=
  ∀ ⦃a b⦄,
    a ∈ doc.lines →
    b ∈ doc.lines →
    a.id = b.id →
    a = b

variable [spec : PositionSpec Position]

def has_present_parents (doc : Document Position Content Peer) : Prop :=
  ∀ line, line ∈ doc.lines →
    line.isBoundary ∨
      ((∃ parent ∈ doc.lines, parent.id = line.fixed.parentLeft) ∧
        ∃ parent ∈ doc.lines, parent.id = line.fixed.parentRight)

def has_parent_intervals (doc : Document Position Content Peer) : Prop :=
  ∀ line, line ∈ doc.lines →
    line.isBoundary ∨
      ∀ left right,
        left ∈ doc.lines →
        left.id = line.fixed.parentLeft →
        right ∈ doc.lines →
        right.id = line.fixed.parentRight →
        left.position < line.position ∧
          line.position < right.position

def has_bottom (doc : Document Position Content Peer) : Prop :=
  ∃ line ∈ doc.lines, line.isBottom

def has_top (doc : Document Position Content Peer) : Prop :=
  ∃ line ∈ doc.lines, line.isTop

structure IsWellFormed (doc : Document Position Content Peer) : Prop where
  unique_ids : has_unique_ids doc
  present_parents : has_present_parents doc
  parent_intervals : has_parent_intervals doc
  bottom : has_bottom doc
  top : has_top doc

-- subtype, a document + what it means to be well-defined/formed.
abbrev WellFormedDocument (Position Content Peer : Type) [PositionSpec Position] :=
  { doc : Document Position Content Peer // IsWellFormed doc }

theorem WellFormedDocument.bottom_unique
    (doc : WellFormedDocument Position Content Peer)
    {a b : Line Position Content Peer}
    (ha : a ∈ doc.val.lines)
    (hb : b ∈ doc.val.lines)
    (ha_id : a.id = LineId.bottom)
    (hb_id : b.id = LineId.bottom) :
    a = b :=
  doc.property.unique_ids ha hb (ha_id.trans hb_id.symm)

theorem WellFormedDocument.top_unique
    (doc : WellFormedDocument Position Content Peer)
    {a b : Line Position Content Peer}
    (ha : a ∈ doc.val.lines)
    (hb : b ∈ doc.val.lines)
    (ha_id : a.id = LineId.top)
    (hb_id : b.id = LineId.top) :
    a = b :=
  doc.property.unique_ids ha hb (ha_id.trans hb_id.symm)

end Syncordian
