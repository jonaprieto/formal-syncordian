import Syncordian.Line

namespace Syncordian

structure Document (Position Content Peer : Type)
    [spec : PositionSpec Position] where
  lines : List (Line Position Content Peer)
  unique_ids : (lines.map (fun line => line.fixed.id)).Nodup
  has_bottom : ∃ line, line ∈ lines ∧
    line.fixed.id = LineId.bottom ∧ line.fixed.position = spec.bottom
  has_top : ∃ line, line ∈ lines ∧
    line.fixed.id = LineId.top ∧ line.fixed.position = spec.top

end Syncordian
