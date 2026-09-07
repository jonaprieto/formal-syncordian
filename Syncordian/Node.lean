import Syncordian.DocumentGenesis
import Syncordian.ReplicaState

namespace Syncordian

variable
  (
    Position
    Content
    Peer
    Tag
    Secret
    Key
    : Type
  )

variable [PositionSpec Position] [LT Peer] [DecidableEq Peer]

structure Configuration
    where
  genesis  : DocumentGenesis Secret Key
  replicas : List (ReplicaState Position Content Peer Tag)

end Syncordian
