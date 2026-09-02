import Syncordian.Line

namespace Syncordian

-- No two lines in a document share an identity.
def has_unique_ids {Position Content Peer : Type}
    (lines : List (Line Position Content Peer)) : Prop :=
  lines |>.map (·.fixed.id) |>.Nodup

structure Document (Position Content Peer : Type)
    [spec : PositionSpec Position] where
  lines : List (Line Position Content Peer)
  unique_ids : has_unique_ids lines
  has_bottom : ∃ line, line ∈ lines ∧
    line.fixed.id = LineId.bottom ∧ line.fixed.position = spec.bottom
  has_top : ∃ line, line ∈ lines ∧
    line.fixed.id = LineId.top ∧ line.fixed.position = spec.top

end Syncordian
