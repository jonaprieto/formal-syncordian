import Syncordian.Signature

namespace Syncordian

-- A document in the network consists of
-- lines + boundary secrets + admissable peers.
variable
  (
    Secret
    Key
    : Type
  )

structure BoundarySecret
    where
  bottom : Secret
  top    : Secret

structure DocumentGenesis
    where
  boundary : BoundarySecret Secret
  keys     : KeyMaterial Key

end Syncordian
