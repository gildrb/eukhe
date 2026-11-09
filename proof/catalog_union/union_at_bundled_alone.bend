# eukhe: the proof of LAW union_at_bundled_alone
#
# PROOF: the union's entry at the bundled entry's place is that entry with
# its twin (pcu.get_bundled); the compiled catalog has no entry with its
# key (pua.find_none), so it has no twin.

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

# no entry has key k: the lookup finds none
def pua.find_none(cs: List<&2, CU.Ent>, +k: Nat, +h: {CatalogUnion.cu_in(CatalogUnion.cu_keys(cs), k) == False{} : Bool}) -> {CU.find(cs, k) == None{} : Maybe<&2, CU.Ent>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +rest:
      match c:
        case CU.Ent{+ck, +ca, +cd, +ct, +cc, +cf, +ch}:
          +hx = LA.pcu.or_false_l(Nat.is_eq(ck, k), CatalogUnion.cu_in(CatalogUnion.cu_keys(rest), k), h)
          +hr = LA.pcu.or_false_r(Nat.is_eq(ck, k), CatalogUnion.cu_in(CatalogUnion.cu_keys(rest), k), h)
          %Equal.sym(Bool, Nat.is_eq(ck, k), False{}, hx) : {CU.find.go(CU.Ent{ck, ca, cd, ct, cc, cf, ch} <> rest, k, _) == None{} : Maybe<&2, CU.Ent>}
          pua.find_none(rest, k, hr)

def pua.main(+bp: List<&2, CU.Ent>, +bq: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +a: Nat, +d: Nat, +t: Maybe<&2, Nat>, +cm: Maybe<&2, Nat>, +ft: Maybe<&2, Nat>, +hd: Maybe<&2, Nat>, hc: {CatalogUnion.cu_in(CatalogUnion.cu_keys(cs), k) == False{} : Bool}) -> {List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), cs), List.length(&2, CU.Ent, bp)) == Some{CU.Ent{k, a, d, t, cm, ft, hd}} : Maybe<&2, CU.Ent>}:
  +g = LA.pcu.get_bundled(bp, CU.Ent{k, a, d, t, cm, ft, hd}, bq, cs, CU.extra(cs, List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq)))
  %Equal.sym(Maybe<&2, CU.Ent>, List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), cs), List.length(&2, CU.Ent, bp)), Some{CU.with(CU.Ent{k, a, d, t, cm, ft, hd}, CU.find(cs, k))}, g) : {_ == Some{CU.Ent{k, a, d, t, cm, ft, hd}} : Maybe<&2, CU.Ent>}
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(cs, k), None{}, pua.find_none(cs, k, hc)) : {Some{CU.with(CU.Ent{k, a, d, t, cm, ft, hd}, _)} == Some{CU.Ent{k, a, d, t, cm, ft, hd}} : Maybe<&2, CU.Ent>}
  {==}

def CatalogUnion.union_at_bundled_alone(bp, bq, cs, k, a, d, t, cm, ft, hd, hc):
  pua.main(bp, bq, cs, k, a, d, t, cm, ft, hd, hc)
