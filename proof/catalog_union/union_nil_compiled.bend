# eukhe: the proof of LAW union_nil_compiled
#
# PROOF: with no compiled entry no bundled entry has a twin, so each
# bundled entry stays as it is, and the compiled-only part is empty.

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

def pun.go(bs: List<&2, CU.Ent>) -> {List.append(&2, CU.Ent, CU.bundled(bs, Nil{}), Nil{}) == bs : List<&2, CU.Ent>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      Equal.cong(List<&2, CU.Ent>, List<&2, CU.Ent>, z => b <> z, List.append(&2, CU.Ent, CU.bundled(rest, Nil{}), Nil{}), rest, pun.go(rest))

def CatalogUnion.union_nil_compiled(bs):
  pun.go(bs)
