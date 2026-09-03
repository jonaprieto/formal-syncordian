import Syncordian.PathId
import Syncordian.Position

namespace Syncordian

def Segment.lt (a b : Segment) : Prop := compare a b = .lt

instance (a b : Segment) : Decidable (Segment.lt a b) := by
  unfold Segment.lt; infer_instance

theorem Segment.compare_def
    (a b : Segment)
    : compare a b = (match compare a.digit b.digit with
                     | .eq => compare a.peer b.peer
                     | result => result) :=
  sorry

theorem Segment.compare_eq_eq
    {a b : Segment}
    : compare a b = .eq ↔ a = b :=
  sorry

theorem Segment.lt_iff
    {a b : Segment}
    : Segment.lt a b ↔ a.digit < b.digit ∨ (a.digit = b.digit ∧ a.peer < b.peer) :=
  sorry

theorem Segment.lt_irrefl (a : Segment) : ¬ Segment.lt a a :=
  sorry

theorem Segment.lt_trans
    {a b c : Segment}
    (hab : Segment.lt a b)
    (hbc : Segment.lt b c)
    : Segment.lt a c :=
  sorry

theorem Segment.lt_total
    (a b : Segment)
    : Segment.lt a b ∨ a = b ∨ Segment.lt b a :=
  sorry

inductive Lex : List Segment → List Segment → Prop
  | nil (b : Segment) (bs : List Segment) : Lex [] (b :: bs)
  | head {a b : Segment} (h : Segment.lt a b) (as bs : List Segment) :
      Lex (a :: as) (b :: bs)
  | tail (a : Segment) {as bs : List Segment} (h : Lex as bs) :
      Lex (a :: as) (a :: bs)

theorem Lex.irrefl : ∀ (as : List Segment), ¬ Lex as as :=
  sorry

theorem Lex.trans : ∀ {as bs cs : List Segment}, Lex as bs → Lex bs cs → Lex as cs :=
  sorry

theorem Lex.total : ∀ (as bs : List Segment), Lex as bs ∨ as = bs ∨ Lex bs as :=
  sorry

theorem Lex.not_nil_right {as : List Segment} : ¬ Lex as [] :=
  sorry

def IsPrefix : List Segment → List Segment → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs => a = b ∧ IsPrefix as bs

theorem Lex.append_right
    : ∀ (as : List Segment) (x : Segment) (xs : List Segment),
        Lex as (as ++ x :: xs) :=
  sorry

theorem Lex.append_of_not_prefix
    : ∀ {as bs : List Segment},
        Lex as bs → ¬ IsPrefix as bs → ∀ x, Lex (as ++ [x]) bs :=
  sorry

theorem Lex.prefix_below
    : ∀ {as bs : List Segment},
        IsPrefix as bs → Lex as bs → Lex as (belowL bs) :=
  sorry

theorem lex_iff_compareList
    : ∀ (as bs : List Segment),
        Lex as bs ↔ Path.compareList as bs = .lt :=
  sorry

theorem belowL_lt
    : ∀ (s : Segment) (ts : List Segment),
        0 < (lastSegOf s ts).peer → Lex (belowL (s :: ts)) (s :: ts) :=
  sorry

theorem Path.below_lt
    (p : Path)
    (hp : p.WellFormed)
    : Lex p.below.toList p.toList :=
  sorry

theorem Path.lt_ext (p : Path) : Lex p.toList p.ext.toList :=
  sorry

def PathId.lt (a b : PathId) : Prop := compare a b = .lt

instance instDecidablePathIdLt (a b : PathId) : Decidable (PathId.lt a b) := by
  unfold PathId.lt; infer_instance

theorem PathId.lt_path
    {p q : Path}
    : PathId.lt (.path p) (.path q) ↔ Lex p.toList q.toList :=
  sorry

theorem PathId.not_lt_infimum (x : PathId) : ¬ PathId.lt x .infimum :=
  sorry

theorem PathId.not_supremum_lt (x : PathId) : ¬ PathId.lt .supremum x :=
  sorry

theorem PathId.infimum_lt
    {x : PathId}
    (h : x ≠ .infimum)
    : PathId.lt .infimum x :=
  sorry

theorem PathId.lt_supremum
    {x : PathId}
    (h : x ≠ .supremum)
    : PathId.lt x .supremum :=
  sorry

theorem PathId.lt_irrefl (x : PathId) : ¬ PathId.lt x x :=
  sorry

theorem PathId.lt_trans
    {a b c : PathId}
    (hab : PathId.lt a b)
    (hbc : PathId.lt b c)
    : PathId.lt a c :=
  sorry

theorem PathId.lt_total
    (a b : PathId)
    (h : a ≠ b)
    : PathId.lt a b ∨ PathId.lt b a :=
  sorry

instance : PositionSpec { x : PathId // x.WellFormed } where
  ltPos a b := PathId.lt a.val b.val
  bottom := ⟨.infimum, trivial⟩
  top := ⟨.supremum, trivial⟩
  irrefl := sorry
  trans := sorry
  total := sorry
  bottom_lt := sorry
  lt_top := sorry
  dense := sorry

instance instDecidableLtWellFormed
    (a b : { x : PathId // x.WellFormed })
    : Decidable (a < b) :=
  instDecidablePathIdLt a.val b.val

end Syncordian
