namespace Syncordian

-- Lifecycle of a document line. A join-semilattice chain: status only moves
-- forward, so concurrent updates join by taking the larger one.
-- Ref: Syncordian.Basic_Types
inductive Status where
  | aura      -- inserted, not yet acknowledged by every trusted peer
  | settled   -- acknowledged by the whole network (response checklist complete)
  | tombstone -- deleted, still in the document (signatures chain through it), absorbing
deriving DecidableEq, Repr, Ord

-- Embedding of the chain into Nat, so the order below is just `≤` on Nat.
def Status.rank : Status → Nat
  | .aura => 0
  | .settled => 1
  | .tombstone => 2

-- Legal transitions: forward along the chain only. No demotion.
def Status.canBecome (before after : Status) : Prop :=
  before.rank ≤ after.rank

instance : LE Status where
  le := Status.canBecome

instance : DecidableLE Status :=
  fun a b => Nat.decLe a.rank b.rank

instance : Max Status where
  max a b := if a ≤ b then b else a

instance : Min Status where
  min a b := if a ≤ b then a else b

#guard max (.aura : Status) .tombstone = .tombstone
#guard min (.aura : Status) .settled = .aura

theorem Status.compare_eq_rank (a b : Status) :
    compare a b = compare a.rank b.rank := by
  cases a <;> cases b <;> rfl

theorem Status.canBecome_refl (s : Status) : s.canBecome s := by
  exact Nat.le_refl _

theorem Status.canBecome_trans {a b c : Status}
    (hab : a.canBecome b) (hbc : b.canBecome c) : a.canBecome c := by
  exact Nat.le_trans hab hbc

-- A settled line is never demoted back to aura.
theorem Status.settled_not_aura : ¬ Status.settled.canBecome .aura := by
  simp [Status.canBecome, Status.rank]

-- The three forward steps of the chain.
theorem Status.aura_to_settled : Status.aura.canBecome .settled := by
  simp [Status.canBecome, Status.rank]

theorem Status.settled_to_tombstone : Status.settled.canBecome .tombstone := by
  simp [Status.canBecome, Status.rank]

theorem Status.aura_to_tombstone : Status.aura.canBecome .tombstone := by
  simp [Status.canBecome, Status.rank]

end Syncordian
