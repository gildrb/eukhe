# eukhe: the proof of LAW union_bundled_only

import Base
import ../../bend/catalog_union.bend as CU
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pcu.bundled_only(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +b: CU.Ent, hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == None{} : Maybe<&2, CU.Ent>}) -> {CU.find(CU.union(bs, cs), k) == Some{b} : Maybe<&2, CU.Ent>}:
  LA.pcu.at(bs, cs, k, Some{b}, None{}, hb, hc)

def Laws.union_bundled_only(bs, cs, k, b, hb, hc):
  pcu.bundled_only(bs, cs, k, b, hb, hc)
