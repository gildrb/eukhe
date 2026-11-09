# eukhe: the proof of LAW union_at_both_same_api
#
# PROOF: the union's entry at the bundled entry's place is that entry
# merged with its twin, the first compiled entry with its key
# (pcu.at_twin); with the same api the merge fills each optional field
# as Maybe.or does (pas.fills: the api test is True, pcu.is_eq_refl).

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

# a field with the same api: the bundled one when stated, else the twin's
def pas.fill_or(t: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> {CU.fill(t, c, True{}) == Maybe.or(&2, Nat, t, c) : Maybe<&2, Nat>}:
  match t:
    case None{}:
      {==}
    case Some{v}:
      {==}

# the four fields filled under a True api test, each Maybe.or
def pas.fills(s: Bool, +k: Nat, +a: Nat, +d: Nat, +t: Maybe<&2, Nat>, +cm: Maybe<&2, Nat>, +ft: Maybe<&2, Nat>, +hd: Maybe<&2, Nat>, +ct: Maybe<&2, Nat>, +cc: Maybe<&2, Nat>, +cf: Maybe<&2, Nat>, +ch: Maybe<&2, Nat>, hs: {s == True{} : Bool}) -> {CU.Ent{k, a, d, CU.fill(t, ct, s), CU.fill(cm, cc, s), CU.fill(ft, cf, s), CU.fill(hd, ch, s)} == CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)} : CU.Ent}:
  match s:
    case False{}:
      LA.pcu.absurdF({CU.Ent{k, a, d, CU.fill(t, ct, False{}), CU.fill(cm, cc, False{}), CU.fill(ft, cf, False{}), CU.fill(hd, ch, False{})} == CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)} : CU.Ent}, hs)
    case True{}:
      %Equal.sym(Maybe<&2, Nat>, CU.fill(t, ct, True{}), Maybe.or(&2, Nat, t, ct), pas.fill_or(t, ct)) : {CU.Ent{k, a, d, _, CU.fill(cm, cc, True{}), CU.fill(ft, cf, True{}), CU.fill(hd, ch, True{})} == CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)} : CU.Ent}
      %Equal.sym(Maybe<&2, Nat>, CU.fill(cm, cc, True{}), Maybe.or(&2, Nat, cm, cc), pas.fill_or(cm, cc)) : {CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), _, CU.fill(ft, cf, True{}), CU.fill(hd, ch, True{})} == CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)} : CU.Ent}
      %Equal.sym(Maybe<&2, Nat>, CU.fill(ft, cf, True{}), Maybe.or(&2, Nat, ft, cf), pas.fill_or(ft, cf)) : {CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), _, CU.fill(hd, ch, True{})} == CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)} : CU.Ent}
      %Equal.sym(Maybe<&2, Nat>, CU.fill(hd, ch, True{}), Maybe.or(&2, Nat, hd, ch), pas.fill_or(hd, ch)) : {CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), _} == CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)} : CU.Ent}
      {==}

def pas.main(+bp: List<&2, CU.Ent>, +bq: List<&2, CU.Ent>, +cp: List<&2, CU.Ent>, +cq: List<&2, CU.Ent>, +k: Nat, +a: Nat, +d: Nat, +t: Maybe<&2, Nat>, +cm: Maybe<&2, Nat>, +ft: Maybe<&2, Nat>, +hd: Maybe<&2, Nat>, +cd: Nat, +ct: Maybe<&2, Nat>, +cc: Maybe<&2, Nat>, +cf: Maybe<&2, Nat>, +ch: Maybe<&2, Nat>, hp: {CatalogUnion.cu_in(CatalogUnion.cu_keys(cp), k) == False{} : Bool}) -> {List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, a, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)) == Some{CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)}} : Maybe<&2, CU.Ent>}:
  +g = LA.pcu.at_twin(bp, bq, cp, cq, k, a, d, t, cm, ft, hd, a, cd, ct, cc, cf, ch, hp)
  %Equal.sym(Maybe<&2, CU.Ent>, List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, a, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)), Some{CU.merge(CU.Ent{k, a, d, t, cm, ft, hd}, CU.Ent{k, a, cd, ct, cc, cf, ch})}, g) : {_ == Some{CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)}} : Maybe<&2, CU.Ent>}
  Equal.cong(CU.Ent, Maybe<&2, CU.Ent>, z => Some{z}, CU.Ent{k, a, d, CU.fill(t, ct, Nat.is_eq(a, a)), CU.fill(cm, cc, Nat.is_eq(a, a)), CU.fill(ft, cf, Nat.is_eq(a, a)), CU.fill(hd, ch, Nat.is_eq(a, a))}, CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)}, pas.fills(Nat.is_eq(a, a), k, a, d, t, cm, ft, hd, ct, cc, cf, ch, LA.pcu.is_eq_refl(a)))

def CatalogUnion.union_at_both_same_api(bp, bq, cp, cq, k, a, d, t, cm, ft, hd, cd, ct, cc, cf, ch, hp):
  pas.main(bp, bq, cp, cq, k, a, d, t, cm, ft, hd, cd, ct, cc, cf, ch, hp)
