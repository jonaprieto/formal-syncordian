import Syncordian.Operation

namespace Syncordian

variable
  (
    Position
    Content
    Peer
    Tag
    : Type
  )

structure Message
    where
  operation    : Operation Position Content Peer Tag
  admissionTag : Tag
deriving DecidableEq, Repr

end Syncordian
