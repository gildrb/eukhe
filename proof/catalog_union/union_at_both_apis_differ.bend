# eukhe: the proof of LAW union_at_both_apis_differ
#
# PROOF: the union's entry at the bundled entry's place is that entry
# merged with its twin, the first compiled entry with its key
# (pcu.at_twin); with another api the merge keeps each optional field
# as the bundle states it (pad.kept: the api test is False).

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

# a field with another api: the bundled one, stated or not
def pad.fill_kept(t: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> {CU.fill(t, c, False{}) == t : Maybe<&2, Nat>}:
  match t:
    case None{}:
      {==}
    case Some{v}:
      {==}

# the four fields filled under a False api test, each the bundled one
def pad.kept(s: Bool, +k: Nat, +a: Nat, +d: Nat, +t: Maybe<&2, Nat>, +cm: Maybe<&2, Nat>, +ft: Maybe<&2, Nat>, +hd: Maybe<&2, Nat>, +ct: Maybe<&2, Nat>, +cc: Maybe<&2, Nat>, +cf: Maybe<&2, Nat>, +ch: Maybe<&2, Nat>, hs: {s == False{} : Bool}) -> {CU.Ent{k, a, d, CU.fill(t, ct, s), CU.fill(cm, cc, s), CU.fill(ft, cf, s), CU.fill(hd, ch, s)} == CU.Ent{k, a, d, t, cm, ft, hd} : CU.Ent}:
  match s:
    case True{}:
      LA.pcu.absurdF({CU.Ent{k, a, d, CU.fill(t, ct, True{}), CU.fill(cm, cc, True{}), CU.fill(ft, cf, True{}), CU.fill(hd, ch, True{})} == CU.Ent{k, a, d, t, cm, ft, hd} : CU.Ent}, Equal.sym(Bool, True{}, False{}, hs))
    case False{}:
      %Equal.sym(Maybe<&2, Nat>, CU.fill(t, ct, False{}), t, pad.fill_kept(t, ct)) : {CU.Ent{k, a, d, _, CU.fill(cm, cc, False{}), CU.fill(ft, cf, False{}), CU.fill(hd, ch, False{})} == CU.Ent{k, a, d, t, cm, ft, hd} : CU.Ent}
      %Equal.sym(Maybe<&2, Nat>, CU.fill(cm, cc, False{}), cm, pad.fill_kept(cm, cc)) : {CU.Ent{k, a, d, t, _, CU.fill(ft, cf, False{}), CU.fill(hd, ch, False{})} == CU.Ent{k, a, d, t, cm, ft, hd} : CU.Ent}
      %Equal.sym(Maybe<&2, Nat>, CU.fill(ft, cf, False{}), ft, pad.fill_kept(ft, cf)) : {CU.Ent{k, a, d, t, cm, _, CU.fill(hd, ch, False{})} == CU.Ent{k, a, d, t, cm, ft, hd} : CU.Ent}
      %Equal.sym(Maybe<&2, Nat>, CU.fill(hd, ch, False{}), hd, pad.fill_kept(hd, ch)) : {CU.Ent{k, a, d, t, cm, ft, _} == CU.Ent{k, a, d, t, cm, ft, hd} : CU.Ent}
      {==}

def pad.main(+bp: List<&2, CU.Ent>, +bq: List<&2, CU.Ent>, +cp: List<&2, CU.Ent>, +cq: List<&2, CU.Ent>, +k: Nat, +a: Nat, +d: Nat, +t: Maybe<&2, Nat>, +cm: Maybe<&2, Nat>, +ft: Maybe<&2, Nat>, +hd: Maybe<&2, Nat>, +ca: Nat, +cd: Nat, +ct: Maybe<&2, Nat>, +cc: Maybe<&2, Nat>, +cf: Maybe<&2, Nat>, +ch: Maybe<&2, Nat>, hp: {CatalogUnion.cu_in(CatalogUnion.cu_keys(cp), k) == False{} : Bool}, ha: {Nat.is_eq(a, ca) == False{} : Bool}) -> {List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)) == Some{CU.Ent{k, a, d, t, cm, ft, hd}} : Maybe<&2, CU.Ent>}:
  +g = LA.pcu.at_twin(bp, bq, cp, cq, k, a, d, t, cm, ft, hd, ca, cd, ct, cc, cf, ch, hp)
  %Equal.sym(Maybe<&2, CU.Ent>, List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)), Some{CU.merge(CU.Ent{k, a, d, t, cm, ft, hd}, CU.Ent{k, ca, cd, ct, cc, cf, ch})}, g) : {_ == Some{CU.Ent{k, a, d, t, cm, ft, hd}} : Maybe<&2, CU.Ent>}
  Equal.cong(CU.Ent, Maybe<&2, CU.Ent>, z => Some{z}, CU.Ent{k, a, d, CU.fill(t, ct, Nat.is_eq(a, ca)), CU.fill(cm, cc, Nat.is_eq(a, ca)), CU.fill(ft, cf, Nat.is_eq(a, ca)), CU.fill(hd, ch, Nat.is_eq(a, ca))}, CU.Ent{k, a, d, t, cm, ft, hd}, pad.kept(Nat.is_eq(a, ca), k, a, d, t, cm, ft, hd, ct, cc, cf, ch, ha))

def CatalogUnion.union_at_both_apis_differ(bp, bq, cp, cq, k, a, d, t, cm, ft, hd, ca, cd, ct, cc, cf, ch, hp, ha):
  pad.main(bp, bq, cp, cq, k, a, d, t, cm, ft, hd, ca, cd, ct, cc, cf, ch, hp, ha)
