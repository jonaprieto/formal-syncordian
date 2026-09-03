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

end Syncordian
