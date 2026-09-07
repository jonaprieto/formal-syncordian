import Syncordian.Line

namespace Syncordian

variable (
    Position
    Content
    Peer
    : Type)

-- A document stores only its ordinary lines. `bottom` and `top` are supplied by
-- `line?` and `lines` instead of being stored, so no invariant has to keep them
-- present, unique or settled.
structure Document
    where
  normalLines : List (NormalLine Position Content Peer)

variable {Position Content Peer}

def Document.empty
    : Document Position Content Peer :=
  { normalLines := [] }

instance : Inhabited (Document Position Content Peer) :=
  { default := Document.empty }

def Document.normalLine?
    [DecidableEq Peer]
    (doc : Document Position Content Peer)
    (id : OpId Peer)
    : Option (NormalLine Position Content Peer) :=
  doc.normalLines.find? fun line => decide (line.id = id)

def Document.line?
    [DecidableEq Peer]
    (doc : Document Position Content Peer)
    : LineId Peer → Option (Line Position Content Peer)
  | .bottom       => some .bottom
  | .top          => some .top
  | .operation id => (doc.normalLine? id).map .normal

-- The boundaries resolve in every document, by definition.
@[simp]
theorem Document.line?_bottom
    [DecidableEq Peer]
    (doc : Document Position Content Peer)
    : doc.line? .bottom = some .bottom :=
  rfl

@[simp]
theorem Document.line?_top
    [DecidableEq Peer]
    (doc : Document Position Content Peer)
    : doc.line? .top = some .top :=
  rfl

-- The virtual list, for statements that need the whole document.
def Document.lines
    (doc : Document Position Content Peer)
    : List (Line Position Content Peer) :=
  .bottom :: doc.normalLines.map Line.normal ++ [.top]

def Document.visibleLines
    (doc : Document Position Content Peer)
    : List (NormalLine Position Content Peer) :=
  doc.normalLines.filter fun line => line.status != .tombstone

def Document.read
    (doc : Document Position Content Peer)
    : List Content :=
  doc.visibleLines.map (·.fixed.content)

-- Only an ordinary line is mutable, so the target is an `OpId`, never a `LineId`.
def Document.updateNormal
    [DecidableEq Peer]
    (doc : Document Position Content Peer)
    (id : OpId Peer)
    (f : NormalLine Position Content Peer → NormalLine Position Content Peer)
    : Document Position Content Peer :=
  { normalLines := doc.normalLines.map fun line => if line.id = id then f line else line }

-- No two stored lines share an identity.
def Document.HasUniqueIds
    (doc : Document Position Content Peer)
    : Prop :=
  (doc.normalLines.map (·.id)).Nodup

-- Both parents of a stored line resolve, through `line?`, to a line of this document.
def Document.HasPresentParents
    [DecidableEq Peer]
    (doc : Document Position Content Peer)
    : Prop :=
  ∀ line ∈ doc.normalLines,
    (doc.line? line.parentLeft).isSome ∧
      (doc.line? line.parentRight).isSome

-- A stored line sits strictly between the positions of its parents.
def Document.HasParentIntervals
    [PositionSpec Position]
    [DecidableEq Peer]
    (doc : Document Position Content Peer)
    : Prop :=
  ∀ line ∈ doc.normalLines,
    ∀ left right,
      doc.line? line.parentLeft = some left →
      doc.line? line.parentRight = some right →
      left.position < line.position ∧
        line.position < right.position

def Document.ParentBefore
    (doc : Document Position Content Peer)
    (parent child : LineId Peer)
    : Prop :=
  ∃ line ∈ doc.normalLines,
    child = .operation line.id ∧
      (parent = line.parentLeft ∨ parent = line.parentRight)

-- Every ancestor chain is finite, which is acyclicity for a finite document.
-- `HasParentIntervals` is spatial correctness; this is the temporal half, and a
-- document needs both.
def Document.ParentRanked
    (doc : Document Position Content Peer)
    : Prop :=
  WellFounded doc.ParentBefore

def Document.ParentRankedBy
    (doc : Document Position Content Peer)
    (parentRank : LineId Peer → Nat)
    : Prop :=
  ∀ parent child, doc.ParentBefore parent child → parentRank parent < parentRank child

theorem Document.parentRanked_of_parentRankedBy
    {doc : Document Position Content Peer}
    {parentRank : LineId Peer → Nat}
    (ranked : doc.ParentRankedBy parentRank)
    : doc.ParentRanked :=
  Subrelation.wf (fun {_ _} step => ranked _ _ step) (InvImage.wf parentRank Nat.lt_wfRel.wf)

def Document.HasSortedLines
    [PositionSpec Position]
    [LT Peer]
    (doc : Document Position Content Peer)
    : Prop :=
  doc.normalLines.Pairwise fun a b => Line.lt (.normal a) (.normal b)

structure Document.WellFormed
    [PositionSpec Position]
    [LT Peer]
    [DecidableEq Peer]
    (doc : Document Position Content Peer)
    : Prop where
  uniqueIds       : Document.HasUniqueIds doc
  presentParents  : Document.HasPresentParents doc
  parentIntervals : Document.HasParentIntervals doc
  parentRanked    : Document.ParentRanked doc
  sortedLines     : Document.HasSortedLines doc

-- subtype, a document + what it means to be well-defined/formed.
abbrev WellFormedDocument
    ( Position
      Content
      Peer
      : Type)
    [PositionSpec Position]
    [LT Peer]
    [DecidableEq Peer]
    :=
  { doc : Document Position Content Peer // Document.WellFormed doc }

end Syncordian
