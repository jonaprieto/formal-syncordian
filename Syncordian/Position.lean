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

def compareLists : List Segment → List Segment → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      match compare a b with
      | .eq => compareLists as bs
      | result => result

instance : Ord Path where
  compare a b := compareLists a.toList b.toList

inductive RawPosition where
  | bottom
  | path (value : Path)
  | top
deriving DecidableEq, Repr

instance : Ord RawPosition where
  compare
    | .bottom, .bottom => .eq
    | .bottom, _ => .lt
    | _, .bottom => .gt
    | .top, .top => .eq
    | .top, _ => .gt
    | _, .top => .lt
    | .path a, .path b => compare a b

def StrictlyBetween (left middle right : RawPosition) : Prop :=
  compare left middle = .lt ∧ compare middle right = .lt

class PositionSpec (α : Type) where
  ltPos : α → α → Prop
  bottom : α
  top : α
  irrefl : ∀ x, ¬ ltPos x x
  trans : ∀ {a b c}, ltPos a b → ltPos b c → ltPos a c
  total : ∀ a b, a ≠ b → ltPos a b ∨ ltPos b a
  bottom_lt : ∀ {x}, x ≠ bottom → ltPos bottom x
  lt_top : ∀ {x}, x ≠ top → ltPos x top
  dense : ∀ {a b}, ltPos a b → ∃ c, ltPos a c ∧ ltPos c b

instance [spec : PositionSpec α] : LT α where
  lt := spec.ltPos

theorem exists_middle {α : Type} [spec : PositionSpec α] {a b : α}
    (h : spec.ltPos a b) : ∃ c, spec.ltPos a c ∧ spec.ltPos c b :=
  spec.dense h

def p1 : RawPosition := .path { head := { digit := 3, peer := 1 }, tail := [] }
def p2 : RawPosition := .path { head := { digit := 3, peer := 1 }, tail := [{ digit := 7, peer := 2 }] }

theorem bottom_lt_path (p : Path) :
    compare RawPosition.bottom (.path p) = .lt := by
  rfl

theorem path_lt_top (p : Path) :
    compare (.path p) RawPosition.top = .lt := by
  rfl

theorem path_between_boundaries (p : Path) :
    StrictlyBetween RawPosition.bottom (.path p) RawPosition.top := by
  constructor <;> rfl

example : compare p1 p2 = .lt := by rfl

end Syncordian
