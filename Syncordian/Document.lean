import Syncordian.Line

namespace Syncordian

structure Document
  (Position
   Content
   Peer
   : Type)
  where
  lines : List (Line Position Content Peer)

end Syncordian
