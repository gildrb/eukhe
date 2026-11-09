# eukhe: the proof of LAW union_nil_bundled
#
# PROOF: the bundled part of an empty bundle is empty, and an empty
# bundle has no key, so every compiled entry stays, in order.

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

def pub.go(cs: List<&2, CU.Ent>) -> {CU.extra(cs, Nil{}) == cs : List<&2, CU.Ent>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      Equal.cong(List<&2, CU.Ent>, List<&2, CU.Ent>, z => c <> z, CU.extra(rest, Nil{}), rest, pub.go(rest))

def CatalogUnion.union_nil_bundled(cs):
  pub.go(cs)
