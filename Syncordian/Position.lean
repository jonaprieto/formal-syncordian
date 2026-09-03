namespace Syncordian

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

theorem exists_middle
    {α : Type}
    [spec : PositionSpec α]
    {a b : α}
    (h : a < b)
    : ∃ c, a < c ∧ c < b :=
  spec.dense h

end Syncordian
