# eukhe: the proof of LAW union_at_both_keeps_bundled
#
# PROOF: the union's entry at the bundled entry's place is that entry
# merged with its twin, the first compiled entry with its key, as field
# fld shows it (pcu.at_both); the bundled entry states the field.

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

def pak.main(+bp: List<&2, CU.Ent>, +bq: List<&2, CU.Ent>, +cp: List<&2, CU.Ent>, +cq: List<&2, CU.Ent>, +k: Nat, +a: Nat, +d: Nat, +t: Maybe<&2, Nat>, +cm: Maybe<&2, Nat>, +ft: Maybe<&2, Nat>, +hd: Maybe<&2, Nat>, +ca: Nat, +cd: Nat, +ct: Maybe<&2, Nat>, +cc: Maybe<&2, Nat>, +cf: Maybe<&2, Nat>, +ch: Maybe<&2, Nat>, +fld: CU.Fld, +v: Nat, hp: {CatalogUnion.cu_in(CatalogUnion.cu_keys(cp), k) == False{} : Bool}, hv: {CU.Ent.opt(CU.Ent{k, a, d, t, cm, ft, hd}, fld) == Some{v} : Maybe<&2, Nat>}) -> {CU.slot(List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)), fld) == Some{CU.Slot{k, a, d, Some{v}}} : Maybe<&2, CU.Slot>}:
  %Equal.sym(Maybe<&2, CU.Slot>, CU.slot(List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)), fld), Some{CU.Slot{k, a, d, CU.fill(CU.Ent.opt(CU.Ent{k, a, d, t, cm, ft, hd}, fld), CU.Ent.opt(CU.Ent{k, ca, cd, ct, cc, cf, ch}, fld), Nat.is_eq(a, ca))}}, LA.pcu.at_both(bp, bq, cp, cq, k, a, d, t, cm, ft, hd, ca, cd, ct, cc, cf, ch, fld, hp)) : {_ == Some{CU.Slot{k, a, d, Some{v}}} : Maybe<&2, CU.Slot>}
  %Equal.sym(Maybe<&2, Nat>, CU.Ent.opt(CU.Ent{k, a, d, t, cm, ft, hd}, fld), Some{v}, hv) : {Some{CU.Slot{k, a, d, CU.fill(_, CU.Ent.opt(CU.Ent{k, ca, cd, ct, cc, cf, ch}, fld), Nat.is_eq(a, ca))}} == Some{CU.Slot{k, a, d, Some{v}}} : Maybe<&2, CU.Slot>}
  {==}

def CatalogUnion.union_at_both_keeps_bundled(bp, bq, cp, cq, k, a, d, t, cm, ft, hd, ca, cd, ct, cc, cf, ch, fld, v, hp, hv):
  pak.main(bp, bq, cp, cq, k, a, d, t, cm, ft, hd, ca, cd, ct, cc, cf, ch, fld, v, hp, hv)
