# eukhe: the proof of LAW union_both_fills_from_compiled

import Base
import ../../bend/catalog_union.bend as CU
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pcu.both_fills(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +b: CU.Ent, +c: CU.Ent, +f: CU.Fld, hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}, hn: {CU.Ent.opt(b, f) == None{} : Maybe<&2, Nat>}, ha: {Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)) == True{} : Bool}) -> {CU.slot(CU.find(CU.union(bs, cs), k), f) == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.Ent.opt(c, f)}} : Maybe<&2, CU.Slot>}:
  %Equal.sym(Maybe<&2, CU.Slot>, CU.slot(CU.find(CU.union(bs, cs), k), f), Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(CU.Ent.opt(b, f), CU.Ent.opt(c, f), Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)))}}, LA.pcu.both(bs, cs, k, b, c, f, hb, hc)) : {_ == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.Ent.opt(c, f)}} : Maybe<&2, CU.Slot>}
  %Equal.sym(Maybe<&2, Nat>, CU.Ent.opt(b, f), None{}, hn) : {Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(_, CU.Ent.opt(c, f), Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)))}} == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.Ent.opt(c, f)}} : Maybe<&2, CU.Slot>}
  %Equal.sym(Bool, Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)), True{}, ha) : {Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(None{}, CU.Ent.opt(c, f), _)}} == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.Ent.opt(c, f)}} : Maybe<&2, CU.Slot>}
  {==}

def Laws.union_both_fills_from_compiled(bs, cs, k, b, c, f, hb, hc, hn, ha):
  pcu.both_fills(bs, cs, k, b, c, f, hb, hc, hn, ha)
