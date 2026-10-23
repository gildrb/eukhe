# eukhe: the proof of LAW union_both_keeps_bundled

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

def pcu.both_keeps_bundled(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +b: CU.Ent, +c: CU.Ent, +f: CU.Fld, +v: Nat, hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}, hv: {CU.Ent.opt(b, f) == Some{v} : Maybe<&2, Nat>}) -> {CU.slot(CU.find(CU.union(bs, cs), k), f) == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), Some{v}}} : Maybe<&2, CU.Slot>}:
  %Equal.sym(Maybe<&2, CU.Slot>, CU.slot(CU.find(CU.union(bs, cs), k), f), Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(CU.Ent.opt(b, f), CU.Ent.opt(c, f), Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)))}}, LA.pcu.both(bs, cs, k, b, c, f, hb, hc)) : {_ == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), Some{v}}} : Maybe<&2, CU.Slot>}
  %Equal.sym(Maybe<&2, Nat>, CU.Ent.opt(b, f), Some{v}, hv) : {Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(_, CU.Ent.opt(c, f), Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)))}} == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), Some{v}}} : Maybe<&2, CU.Slot>}
  {==}

def CatalogUnion.union_both_keeps_bundled(bs, cs, k, b, c, f, v, hb, hc, hv):
  pcu.both_keeps_bundled(bs, cs, k, b, c, f, v, hb, hc, hv)
