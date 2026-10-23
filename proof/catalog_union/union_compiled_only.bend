# eukhe: the proof of LAW union_compiled_only

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

def pcu.compiled_only(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +c: CU.Ent, hb: {CU.find(bs, k) == None{} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}) -> {CU.find(CU.union(bs, cs), k) == Some{c} : Maybe<&2, CU.Ent>}:
  LA.pcu.at(bs, cs, k, None{}, Some{c}, hb, hc)

def CatalogUnion.union_compiled_only(bs, cs, k, c, hb, hc):
  pcu.compiled_only(bs, cs, k, c, hb, hc)
