import Syncordian.Segment

namespace Syncordian

structure Path where
  head : Segment
  tail : List Segment
deriving DecidableEq, Repr

def Path.toList
    (p : Path)
    : List Segment :=
  p.head :: p.tail

def Path.compareList
    : List Segment →
      List Segment → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      match compare a b with
      | .eq => Path.compareList as bs
      | result => result

instance : Ord Path where
  compare a b := Path.compareList a.toList b.toList

end Syncordian
