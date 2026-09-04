import Syncordian.LineId

namespace Syncordian

variable (
    Peer
    : Type)

-- the pair of parent lines that defines the interval where a block began.
-- The session identifies the authored block.
structure Session
    where
  left  : LineId Peer
  right : LineId Peer
deriving DecidableEq, Repr

end Syncordian
