-- Ref: Syncordian.PathId
namespace Syncordian

structure Segment where
  digit : Nat
  peer : Nat
deriving DecidableEq, Repr

instance : Ord Segment where
  compare a b :=
    match compare a.digit b.digit with
    | .eq => compare a.peer b.peer
    | result => result

structure Path where
  head : Segment
  tail : List Segment
deriving DecidableEq, Repr

def Path.toList (p : Path) : List Segment := p.head :: p.tail

def Path.compareList : List Segment → List Segment → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      match compare a b with
      | .eq => Path.compareList as bs
      | result => result

instance : Ord Path where
  compare a b := Path.compareList a.toList b.toList

inductive PathId where
  | infimum
  | path (value : Path)
  | supremum
deriving DecidableEq, Repr

instance : Ord PathId where
  compare
    | .infimum, .infimum => .eq
    | .infimum, _ => .lt
    | _, .infimum => .gt
    | .supremum, .supremum => .eq
    | .supremum, _ => .gt
    | _, .supremum => .lt
    | .path a, .path b => compare a b

theorem PathId.infimum_lt_path (p : Path) :
    compare PathId.infimum (.path p) = .lt := by
  rfl

theorem PathId.path_lt_supremum (p : Path) :
    compare (.path p) PathId.supremum = .lt := by
  rfl

#guard compare
    (PathId.path { head := { digit := 3, peer := 1 }, tail := [] })
    (PathId.path { head := { digit := 3, peer := 1 },
                   tail := [{ digit := 7, peer := 2 }] })
  = .lt

def lastSegOf : Segment → List Segment → Segment
  | s, [] => s
  | _, t :: ts => lastSegOf t ts

def Path.lastSeg (p : Path) : Segment := lastSegOf p.head p.tail

def Path.WellFormed (p : Path) : Prop := 0 < p.lastSeg.peer

def PathId.WellFormed : PathId → Prop
  | .path p => p.WellFormed
  | _ => True

instance (p : Path) : Decidable p.WellFormed := by
  unfold Path.WellFormed; infer_instance

instance (x : PathId) : Decidable x.WellFormed := by
  cases x <;> (unfold PathId.WellFormed; infer_instance)

def Segment.least : Segment := { digit := 0, peer := 1 }

def belowL : List Segment → List Segment
  | [] => []
  | [s] => [{ s with peer := s.peer - 1 }, Segment.least]
  | s :: ts => s :: belowL ts

def Path.below (p : Path) : Path :=
  match p.tail with
  | [] => { head := { p.head with peer := p.head.peer - 1 }, tail := [Segment.least] }
  | t :: ts => { head := p.head, tail := belowL (t :: ts) }

theorem Path.below_toList (p : Path) : p.below.toList = belowL p.toList := by
  obtain ⟨hd, tl⟩ := p
  cases tl <;> rfl

theorem lastSegOf_belowL : ∀ (x s : Segment) (ts : List Segment),
    lastSegOf x (belowL (s :: ts)) = Segment.least := by
  intro x s ts
  induction ts generalizing x s with
  | nil => rfl
  | cons t ts ih => exact ih s t

theorem Path.below_wellFormed (p : Path) : p.below.WellFormed := by
  obtain ⟨hd, tl⟩ := p
  cases tl with
  | nil => exact Nat.one_pos
  | cons t ts =>
    show 0 < (lastSegOf hd (belowL (t :: ts))).peer
    rw [lastSegOf_belowL]
    exact Nat.one_pos

theorem belowL_cons : ∀ (s : Segment) (ts : List Segment),
    ∃ (y : Segment) (ys : List Segment), belowL (s :: ts) = y :: ys := by
  intro s ts
  cases ts with
  | nil => exact ⟨_, _, rfl⟩
  | cons t ts => exact ⟨_, _, rfl⟩

def Path.ext (p : Path) : Path := { head := p.head, tail := p.tail ++ [Segment.least] }

theorem Path.ext_toList (p : Path) : p.ext.toList = p.toList ++ [Segment.least] := rfl

theorem lastSegOf_append_least : ∀ (x : Segment) (ys : List Segment),
    lastSegOf x (ys ++ [Segment.least]) = Segment.least := by
  intro x ys
  induction ys generalizing x with
  | nil => rfl
  | cons y ys ih => exact ih y

theorem Path.ext_wellFormed (p : Path) : p.ext.WellFormed := by
  show 0 < (lastSegOf p.head (p.tail ++ [Segment.least])).peer
  rw [lastSegOf_append_least]
  exact Nat.one_pos

theorem Path.toList_inj {p q : Path} (h : p.toList = q.toList) : p = q := by
  obtain ⟨ph, pt⟩ := p
  obtain ⟨qh, qt⟩ := q
  simp [Path.toList] at h
  simp [h.1, h.2]

end Syncordian
