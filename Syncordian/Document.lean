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

def has_present_parents (doc : Document Position Content Peer) : Prop :=
  ∀ line, line ∈ doc.lines →
    line.id = LineId.bottom ∨
      line.id = LineId.top ∨
      ((∃ parent ∈ doc.lines, parent.id = line.fixed.parentLeft) ∧
        ∃ parent ∈ doc.lines, parent.id = line.fixed.parentRight)

variable [spec : PositionSpec Position]

def has_bottom (doc : Document Position Content Peer) : Prop :=
  ∃ line ∈ doc.lines,
    line.id = LineId.bottom ∧ line.position = spec.bottom

def has_top (doc : Document Position Content Peer) : Prop :=
  ∃ line ∈ doc.lines,
    line.id = LineId.top ∧ line.position = spec.top

structure IsWellFormed (doc : Document Position Content Peer) : Prop where
  unique_ids : has_unique_ids doc
  present_parents : has_present_parents doc
  bottom : has_bottom doc
  top : has_top doc

-- subtype, a document + what it means to be well-defined/formed.
abbrev WellFormedDocument (Position Content Peer : Type) [PositionSpec Position] :=
  { doc : Document Position Content Peer // IsWellFormed doc }

theorem WellFormedDocument.bottom_unique
    (doc : WellFormedDocument Position Content Peer)
    {a b : Line Position Content Peer}
    (ha : a ∈ doc.val.lines) (hb : b ∈ doc.val.lines)
    (ha_id : a.id = LineId.bottom)
    (hb_id : b.id = LineId.bottom) :
    a = b :=
  doc.property.unique_ids ha hb (ha_id.trans hb_id.symm)

theorem WellFormedDocument.top_unique
    (doc : WellFormedDocument Position Content Peer)
    {a b : Line Position Content Peer}
    (ha : a ∈ doc.val.lines) (hb : b ∈ doc.val.lines)
    (ha_id : a.id = LineId.top)
    (hb_id : b.id = LineId.top) :
    a = b :=
  doc.property.unique_ids ha hb (ha_id.trans hb_id.symm)

end Syncordian
