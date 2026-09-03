import Syncordian.PathId
import Syncordian.Position

namespace Syncordian

-- Segments order by digit, then by peer.
instance : LT Segment where
  lt a b := a.digit < b.digit ∨ (a.digit = b.digit ∧ a.peer < b.peer)

theorem Segment.lt_def
    {a b : Segment}
    : a < b ↔ a.digit < b.digit ∨ (a.digit = b.digit ∧ a.peer < b.peer) :=
  Iff.rfl

instance (a b : Segment) : Decidable (a < b) :=
  decidable_of_iff _ Segment.lt_def.symm

theorem Segment.compare_eq_eq
    {a b : Segment}
    : compare a b = .eq ↔ a = b := by
  obtain ⟨d1, p1⟩ := a
  obtain ⟨d2, p2⟩ := b
  simp [compare, compareOfLessAndEq]
  grind

-- The only place the order and the executable comparator meet.
theorem Segment.compare_eq_lt
    {a b : Segment}
    : compare a b = .lt ↔ a < b := by
  simp [Segment.lt_def, compare, compareOfLessAndEq]
  grind

theorem Segment.lt_irrefl (a : Segment) : ¬ a < a := by
  grind [Segment.lt_def]

theorem Segment.lt_trans
    {a b c : Segment}
    (hab : a < b)
    (hbc : b < c)
    : a < c := by
  grind [Segment.lt_def]

theorem Segment.lt_total
    (a b : Segment)
    : a < b ∨ a = b ∨ b < a := by
  obtain ⟨d1, p1⟩ := a
  obtain ⟨d2, p2⟩ := b
  simp [Segment.lt_def]
  grind

inductive Lex : List Segment → List Segment → Prop
  | nil (b : Segment) (bs : List Segment) : Lex [] (b :: bs)
  | head {a b : Segment} (h : a < b) (as bs : List Segment) :
      Lex (a :: as) (b :: bs)
  | tail (a : Segment) {as bs : List Segment} (h : Lex as bs) :
      Lex (a :: as) (a :: bs)

theorem Lex.irrefl : ∀ (as : List Segment), ¬ Lex as as := by
  intro as h
  induction as with
  | nil => cases h
  | cons a as ih =>
    cases h with
    | head h _ _ => exact Segment.lt_irrefl a h
    | tail _ h => exact ih h

theorem Lex.trans : ∀ {as bs cs : List Segment}, Lex as bs → Lex bs cs → Lex as cs := by
  intro as
  induction as with
  | nil =>
    intro bs cs _ hbc
    cases hbc with
    | nil b bs => exact Lex.nil _ _
    | head _ _ _ => exact Lex.nil _ _
    | tail _ _ => exact Lex.nil _ _
  | cons a as ih =>
    intro bs cs hab hbc
    cases hab with
    | head hlt _ _ =>
      cases hbc with
      | head hlt' _ _ => exact Lex.head (Segment.lt_trans hlt hlt') _ _
      | tail _ _ => exact Lex.head hlt _ _
    | tail _ h =>
      cases hbc with
      | head hlt' _ _ => exact Lex.head hlt' _ _
      | tail _ h' => exact Lex.tail _ (ih h h')

theorem Lex.total : ∀ (as bs : List Segment), Lex as bs ∨ as = bs ∨ Lex bs as := by
  intro as
  induction as with
  | nil =>
    intro bs
    cases bs with
    | nil => exact Or.inr (Or.inl rfl)
    | cons b bs => exact Or.inl (Lex.nil _ _)
  | cons a as ih =>
    intro bs
    cases bs with
    | nil => exact Or.inr (Or.inr (Lex.nil _ _))
    | cons b bs =>
      rcases Segment.lt_total a b with h | h | h
      · exact Or.inl (Lex.head h _ _)
      · subst h
        rcases ih bs with h' | h' | h'
        · exact Or.inl (Lex.tail _ h')
        · exact Or.inr (Or.inl (by rw [h']))
        · exact Or.inr (Or.inr (Lex.tail _ h'))
      · exact Or.inr (Or.inr (Lex.head h _ _))

theorem Lex.not_nil_right {as : List Segment} : ¬ Lex as [] := by
  intro h; cases h

def IsPrefix : List Segment → List Segment → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs => a = b ∧ IsPrefix as bs

theorem Lex.append_right
    : ∀ (as : List Segment) (x : Segment) (xs : List Segment),
        Lex as (as ++ x :: xs) := by
  intro as x xs
  induction as with
  | nil => exact Lex.nil _ _
  | cons a as ih => exact Lex.tail a ih

theorem Lex.append_of_not_prefix
    : ∀ {as bs : List Segment},
        Lex as bs → ¬ IsPrefix as bs → ∀ x, Lex (as ++ [x]) bs := by
  intro as
  induction as with
  | nil => intro bs _ hnp _; exact absurd trivial hnp
  | cons a as ih =>
    intro bs hlex hnp x
    cases hlex with
    | head h _ _ => exact Lex.head h _ _
    | tail _ h =>
      refine Lex.tail a (ih h ?_ x)
      intro hp
      exact hnp ⟨rfl, hp⟩

theorem Lex.prefix_below
    : ∀ {as bs : List Segment},
        IsPrefix as bs → Lex as bs → Lex as (belowL bs) := by
  intro as
  induction as with
  | nil =>
    intro bs _ hlex
    cases bs with
    | nil => exact absurd hlex Lex.not_nil_right
    | cons b bs =>
      obtain ⟨y, ys, hy⟩ := belowL_cons b bs
      rw [hy]
      exact Lex.nil _ _
  | cons a as ih =>
    intro bs hp hlex
    cases bs with
    | nil => exact absurd hlex Lex.not_nil_right
    | cons b bs =>
      obtain ⟨hab, hp'⟩ := hp
      subst hab
      cases hlex with
      | head h _ _ => exact absurd h (Segment.lt_irrefl a)
      | tail _ h =>
        cases bs with
        | nil => exact absurd h Lex.not_nil_right
        | cons t ts =>
          show Lex (a :: as) (a :: belowL (t :: ts))
          exact Lex.tail a (ih hp' h)

theorem lex_iff_compareList
    : ∀ (as bs : List Segment),
        Lex as bs ↔ Path.compareList as bs = .lt := by
  intro as
  induction as with
  | nil =>
    intro bs
    cases bs with
    | nil => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    | cons b bs => exact ⟨fun _ => rfl, fun _ => Lex.nil _ _⟩
  | cons a as ih =>
    intro bs
    cases bs with
    | nil => exact ⟨fun h => absurd h Lex.not_nil_right, fun h => by cases h⟩
    | cons b bs =>
      show Lex (a :: as) (b :: bs) ↔
        (match compare a b with
         | .eq => Path.compareList as bs
         | result => result) = .lt
      cases hc : compare a b with
      | lt =>
        exact ⟨fun _ => rfl, fun _ => Lex.head (Segment.compare_eq_lt.mp hc) as bs⟩
      | eq =>
        have hab : a = b := Segment.compare_eq_eq.mp hc
        subst hab
        constructor
        · intro h
          cases h with
          | head h' _ _ => exact absurd h' (Segment.lt_irrefl a)
          | tail _ h' => exact (ih bs).mp h'
        · intro h
          exact Lex.tail a ((ih bs).mpr h)
      | gt =>
        constructor
        · intro h
          cases h with
          | head h' _ _ => rw [Segment.compare_eq_lt.mpr h'] at hc; cases hc
          | tail _ _ => rw [Segment.compare_eq_eq.mpr rfl] at hc; cases hc
        · intro h; cases h

theorem belowL_lt
    : ∀ (s : Segment) (ts : List Segment),
        0 < (lastSegOf s ts).peer → Lex (belowL (s :: ts)) (s :: ts) := by
  intro s ts
  induction ts generalizing s with
  | nil =>
    intro h
    have h' : 0 < s.peer := h
    show Lex [{ s with peer := s.peer - 1 }, Segment.least] [s]
    exact Lex.head (a := { s with peer := s.peer - 1 }) (b := s)
      (Or.inr ⟨rfl, Nat.sub_lt h' Nat.one_pos⟩) _ _
  | cons t ts ih =>
    intro h
    exact Lex.tail _ (ih t h)

theorem Path.below_lt
    (p : Path)
    (hp : p.WellFormed)
    : Lex p.below.toList p.toList := by
  rw [Path.below_toList]
  exact belowL_lt p.head p.tail hp

theorem Path.lt_ext (p : Path) : Lex p.toList p.ext.toList := by
  show Lex (p.head :: p.tail) (p.head :: (p.tail ++ [Segment.least]))
  exact Lex.tail p.head (Lex.append_right p.tail Segment.least [])

def PathId.lt (a b : PathId) : Prop := compare a b = .lt

instance instDecidablePathIdLt (a b : PathId) : Decidable (PathId.lt a b) := by
  unfold PathId.lt; infer_instance

theorem PathId.lt_path
    {p q : Path}
    : PathId.lt (.path p) (.path q) ↔ Lex p.toList q.toList :=
  (lex_iff_compareList _ _).symm

theorem PathId.not_lt_infimum (x : PathId) : ¬ PathId.lt x .infimum := by
  cases x <;> (intro h; cases h)

theorem PathId.not_supremum_lt (x : PathId) : ¬ PathId.lt .supremum x := by
  cases x <;> (intro h; cases h)

theorem PathId.infimum_lt
    {x : PathId}
    (h : x ≠ .infimum)
    : PathId.lt .infimum x := by
  cases x with
  | infimum => exact absurd rfl h
  | path _ => rfl
  | supremum => rfl

theorem PathId.lt_supremum
    {x : PathId}
    (h : x ≠ .supremum)
    : PathId.lt x .supremum := by
  cases x with
  | supremum => exact absurd rfl h
  | infimum => rfl
  | path _ => rfl

theorem PathId.lt_irrefl (x : PathId) : ¬ PathId.lt x x := by
  cases x with
  | infimum => intro h; cases h
  | supremum => intro h; cases h
  | path p => rw [PathId.lt_path]; exact Lex.irrefl _

theorem PathId.lt_trans
    {a b c : PathId}
    (hab : PathId.lt a b)
    (hbc : PathId.lt b c)
    : PathId.lt a c := by
  cases a <;> cases b <;> cases c <;>
    first
      | exact absurd hab (PathId.not_supremum_lt _)
      | exact absurd hbc (PathId.not_supremum_lt _)
      | exact absurd hab (PathId.not_lt_infimum _)
      | exact absurd hbc (PathId.not_lt_infimum _)
      | rfl
      | exact PathId.lt_path.mpr (Lex.trans (PathId.lt_path.mp hab) (PathId.lt_path.mp hbc))

theorem PathId.lt_total
    (a b : PathId)
    (h : a ≠ b)
    : PathId.lt a b ∨ PathId.lt b a := by
  cases a <;> cases b <;>
    first
      | exact absurd rfl h
      | exact Or.inl rfl
      | exact Or.inr rfl
      | (rename_i p q
         rcases Lex.total p.toList q.toList with hl | he | hr
         · exact Or.inl (PathId.lt_path.mpr hl)
         · exact absurd (congrArg PathId.path (Path.toList_inj he)) h
         · exact Or.inr (PathId.lt_path.mpr hr))

instance : PositionSpec { x : PathId // x.WellFormed } where
  ltPos a b     := PathId.lt a.val b.val
  bottom        := ⟨.infimum, trivial⟩
  top           := ⟨.supremum, trivial⟩
  irrefl x      := PathId.lt_irrefl x.val
  trans hab hbc := PathId.lt_trans hab hbc
  total a b h   := PathId.lt_total a.val b.val fun hv => h (Subtype.ext hv)
  bottom_lt     := by
    intro x hx
    exact PathId.infimum_lt fun hv => hx (Subtype.ext hv)
  lt_top := by
    intro x hx
    exact PathId.lt_supremum fun hv => hx (Subtype.ext hv)
  dense := by
    intro a b h
    obtain ⟨av, ha⟩ := a
    obtain ⟨bv, hb⟩ := b
    cases av with
    | supremum => exact absurd h (PathId.not_supremum_lt _)
    | infimum =>
      cases bv with
      | infimum => exact absurd h (PathId.not_lt_infimum _)
      | path q =>
        exact ⟨⟨.path q.below, Path.below_wellFormed q⟩, rfl,
          PathId.lt_path.mpr (Path.below_lt q hb)⟩
      | supremum =>
        exact ⟨⟨.path { head := Segment.least, tail := [] }, Nat.one_pos⟩, rfl, rfl⟩
    | path p =>
      cases bv with
      | infimum => exact absurd h (PathId.not_lt_infimum _)
      | supremum =>
        exact ⟨⟨.path p.ext, Path.ext_wellFormed p⟩,
          PathId.lt_path.mpr (Path.lt_ext p), rfl⟩
      | path q =>
        have h' := PathId.lt_path.mp h
        by_cases hpre : IsPrefix p.toList q.toList
        · refine ⟨⟨.path q.below, Path.below_wellFormed q⟩, ?_,
            PathId.lt_path.mpr (Path.below_lt q hb)⟩
          refine PathId.lt_path.mpr ?_
          rw [Path.below_toList]
          exact Lex.prefix_below hpre h'
        · refine ⟨⟨.path p.ext, Path.ext_wellFormed p⟩,
            PathId.lt_path.mpr (Path.lt_ext p), ?_⟩
          refine PathId.lt_path.mpr ?_
          rw [Path.ext_toList]
          exact Lex.append_of_not_prefix h' hpre Segment.least

instance instDecidableLtWellFormed
    (a b : { x : PathId // x.WellFormed })
    : Decidable (a < b) :=
  instDecidablePathIdLt a.val b.val

end Syncordian
