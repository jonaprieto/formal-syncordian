import Syncordian.Line

namespace Syncordian

variable
  (
    Position
    Content
    Peer
    : Type
  )

-- Raw storage holds only ordinary lines. `bottom` and `top` are supplied by
-- `line?` and `lines` instead of being stored, so no invariant has to keep them
-- present, unique or settled.
structure RawDocument
    where
  normalLines : List (NormalLine Position Content Peer)

variable {Position Content Peer}

def RawDocument.empty
    : RawDocument Position Content Peer :=
  { normalLines := [] }

instance : Inhabited (RawDocument Position Content Peer) :=
  { default := RawDocument.empty }

def RawDocument.normalLine?
    [DecidableEq Peer]
    (doc : RawDocument Position Content Peer)
    (id : OpId Peer)
    : Option (NormalLine Position Content Peer) :=
  doc.normalLines.find? fun line => decide (line.id = id)

def RawDocument.line?
    [DecidableEq Peer]
    (doc : RawDocument Position Content Peer)
    : LineId Peer → Option (Line Position Content Peer)
  | .bottom       => some .bottom
  | .top          => some .top
  | .operation id => (doc.normalLine? id).map .normal

-- The boundaries resolve in every document, by definition.
@[simp]
theorem RawDocument.line?_bottom
    [DecidableEq Peer]
    (doc : RawDocument Position Content Peer)
    : doc.line? .bottom = some .bottom :=
  rfl

@[simp]
theorem RawDocument.line?_top
    [DecidableEq Peer]
    (doc : RawDocument Position Content Peer)
    : doc.line? .top = some .top :=
  rfl

-- The virtual list, for statements that need the whole document.
def RawDocument.lines
    (doc : RawDocument Position Content Peer)
    : List (Line Position Content Peer) :=
  .bottom :: doc.normalLines.map Line.normal ++ [.top]

def RawDocument.visibleLines
    (doc : RawDocument Position Content Peer)
    : List (NormalLine Position Content Peer) :=
  doc.normalLines.filter fun line => line.status != .tombstone

def RawDocument.read
    (doc : RawDocument Position Content Peer)
    : List Content :=
  doc.visibleLines.map (·.fixed.content)

-- Only an ordinary line is mutable, so the target is an `OpId`, never a `LineId`.
def RawDocument.updateNormal
    [DecidableEq Peer]
    (doc : RawDocument Position Content Peer)
    (id : OpId Peer)
    (f : NormalLine Position Content Peer → NormalLine Position Content Peer)
    : RawDocument Position Content Peer :=
  { normalLines := doc.normalLines.map fun line => if line.id = id then f line else line }

-- No two stored lines share an identity.
def RawDocument.HasUniqueIds
    (doc : RawDocument Position Content Peer)
    : Prop :=
  (doc.normalLines.map (·.id)).Nodup

-- Both parents of a stored line resolve, through `line?`, to a line of this document.
def RawDocument.HasPresentParents
    [DecidableEq Peer]
    (doc : RawDocument Position Content Peer)
    : Prop :=
  ∀ line ∈ doc.normalLines,
    (doc.line? line.parentLeft).isSome ∧
      (doc.line? line.parentRight).isSome

-- A stored line sits strictly between the positions of its parents.
def RawDocument.HasParentIntervals
    [PositionSpec Position]
    [DecidableEq Peer]
    (doc : RawDocument Position Content Peer)
    : Prop :=
  ∀ line ∈ doc.normalLines,
    ∀ left right,
      doc.line? line.parentLeft = some left →
      doc.line? line.parentRight = some right →
      left.position < line.position ∧
        line.position < right.position

def RawDocument.ParentBefore
    (doc : RawDocument Position Content Peer)
    (parent child : LineId Peer)
    : Prop :=
  ∃ line ∈ doc.normalLines,
    child = .operation line.id ∧
      (parent = line.parentLeft ∨ parent = line.parentRight)

-- Every ancestor chain is finite, which is acyclicity for a finite document.
-- `HasParentIntervals` is spatial correctness; this is the temporal half, and a
-- document needs both.
def RawDocument.ParentRanked
    (doc : RawDocument Position Content Peer)
    : Prop :=
  WellFounded doc.ParentBefore

def RawDocument.ParentRankedBy
    (doc : RawDocument Position Content Peer)
    (parentRank : LineId Peer → Nat)
    : Prop :=
  ∀ parent child, doc.ParentBefore parent child → parentRank parent < parentRank child

theorem RawDocument.parentRanked_of_parentRankedBy
    {doc : RawDocument Position Content Peer}
    {parentRank : LineId Peer → Nat}
    (ranked : doc.ParentRankedBy parentRank)
    : doc.ParentRanked :=
  Subrelation.wf (fun {_ _} step => ranked _ _ step) (InvImage.wf parentRank Nat.lt_wfRel.wf)

def RawDocument.HasSortedLines
    [PositionSpec Position]
    [LT Peer]
    (doc : RawDocument Position Content Peer)
    : Prop :=
  doc.normalLines.Pairwise fun a b => Line.lt (.normal a) (.normal b)

section CertifiedDocument

variable
  [PositionSpec Position]
  [LT Peer]
  [DecidableEq Peer]

structure RawDocument.WellFormed
    (doc : RawDocument Position Content Peer)
    : Prop
    where
  uniqueIds       : RawDocument.HasUniqueIds doc
  presentParents  : RawDocument.HasPresentParents doc
  parentIntervals : RawDocument.HasParentIntervals doc
  parentRanked    : RawDocument.ParentRanked doc
  sortedLines     : RawDocument.HasSortedLines doc

theorem RawDocument.empty_wellFormed
    : (RawDocument.empty : RawDocument Position Content Peer).WellFormed := by
  refine ⟨
    -- uniqueIds
    by simp [RawDocument.empty, RawDocument.HasUniqueIds],
    -- presentParents
    by simp [RawDocument.empty, RawDocument.HasPresentParents, RawDocument.line?],
    -- parentIntervals
    by simp [RawDocument.empty, RawDocument.HasParentIntervals, RawDocument.line?],
    -- parentRanked
    ?_,
    -- sortedLines
    by simp [RawDocument.empty, RawDocument.HasSortedLines]⟩
  refine ⟨fun child => Acc.intro child ?_⟩
  intro parent edge
  simp [RawDocument.empty, RawDocument.ParentBefore] at edge

-- A document is raw storage bundled with its well-formedness certificate.
abbrev Document
    (Position Content Peer : Type)
    [PositionSpec Position]
    [LT Peer]
    [DecidableEq Peer]
    :=
  { doc : RawDocument Position Content Peer // RawDocument.WellFormed doc }

abbrev Document.raw
    (doc : Document Position Content Peer)
    : RawDocument Position Content Peer :=
  doc.val

abbrev Document.wellFormed
    (doc : Document Position Content Peer)
    : doc.raw.WellFormed :=
  doc.property

def Document.empty
    : Document Position Content Peer :=
  ⟨RawDocument.empty, RawDocument.empty_wellFormed⟩

instance
    : Inhabited (Document Position Content Peer) :=
  ⟨Document.empty⟩

end CertifiedDocument

end Syncordian
