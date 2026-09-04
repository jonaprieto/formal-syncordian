namespace Syncordian

structure Segment where
  digit : Nat
  peer  : Nat
deriving DecidableEq, Repr

instance : Ord Segment where
  compare a b :=
    (compare a.digit b.digit).then
      (compare a.peer b.peer)

abbrev lt_seg
    (a b : Segment)
    : Prop :=
  a.digit < b.digit ∨ (a.digit = b.digit ∧ a.peer < b.peer)

-- Segments order by digit, then by peer.
instance : LT Segment where
  lt a b := lt_seg a b

theorem Segment.lt_def
    {a b : Segment}
    : a < b ↔ lt_seg a b :=
  Iff.rfl

instance (a b : Segment) : Decidable (a < b) :=
  decidable_of_iff _ Segment.lt_def.symm

#guard ({ digit := 1, peer := 0 } : Segment) < { digit := 1, peer := 2 }

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
  simp [Segment.lt_def, compare, compareOfLessAndEq, Ordering.then]
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

end Syncordian
