# eukhe: lemmas the proofs of area tree share: maybe

import Base
import ../../../bend/tree.bend as Tr

def pt.has_cons_go(b: Bool, +h: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat) -> {Maybe.is_some(&2, Tr.Ent, Tr.get.go(h <> r, y, b)) == Bool.or(b, Tr.has(r, y)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
