# eukhe: the proof of LAW union_hides_nothing

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

# The laws
# --------

def pcu.some_pick(mb: Maybe<&2, CU.Ent>, +mc: Maybe<&2, CU.Ent>) -> {Maybe.is_some(&2, CU.Ent, LA.pcu.pick(mb, mc)) == Bool.or(Maybe.is_some(&2, CU.Ent, mb), Maybe.is_some(&2, CU.Ent, mc)) : Bool}:
  match mb:
    case None{}:
      {==}
    case Some{b}:
      {==}

def pcu.hides_nothing(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat) -> {CU.has(CU.union(bs, cs), k) == Bool.or(CU.has(bs, k), CU.has(cs, k)) : Bool}:
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(bs, cs), k), LA.pcu.pick(CU.find(bs, k), CU.find(cs, k)), LA.pcu.find_union(bs, cs, k)) : {Maybe.is_some(&2, CU.Ent, _) == Bool.or(CU.has(bs, k), CU.has(cs, k)) : Bool}
  pcu.some_pick(CU.find(bs, k), CU.find(cs, k))

# (C1) The catalog union

def CatalogUnion.union_hides_nothing(bs, cs, k):
  pcu.hides_nothing(bs, cs, k)
