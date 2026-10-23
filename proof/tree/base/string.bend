# eukhe: lemmas the proofs of area tree share: string

import Base
import ../../../bend/ffi_tree.bend as Ft
import ../../../bend/tree.bend as Tr

# the items of a list of ops, then rest
def tf.items(ops: List<&2, Tr.Op>, rest: String) -> String:
  match ops:
    case Nil{}:
      rest
    case o <> r:
      Ft.put_op(o, tf.items(r, rest))
