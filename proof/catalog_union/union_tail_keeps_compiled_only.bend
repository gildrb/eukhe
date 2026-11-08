# eukhe: the proof of LAW union_tail_keeps_compiled_only
#
# PROOF: the union after the bundle's length is the compiled-only part
# (pcu.drop_bundled); it drops a compiled entry only when the bundle has
# its key (pcu.has_in), so never one with key k, which the bundle lacks.

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

def puo.go(seen: Bool, hit: Bool, +ck: Nat, +ca: Nat, +cd: Nat, +ct: Maybe<&2, Nat>, +cc: Maybe<&2, Nat>, +cf: Maybe<&2, Nat>, +ch: Maybe<&2, Nat>, +rest: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, +k: Nat, es: {CU.has(bs, ck) == seen : Bool}, eh: {Nat.is_eq(ck, k) == hit : Bool}, hb: {CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k) == False{} : Bool}, ih: {CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra(rest, bs)), k) == CatalogUnion.cu_times(CatalogUnion.cu_keys(rest), k) : Nat}) -> {CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra.go(CU.Ent{ck, ca, cd, ct, cc, cf, ch} <> rest, bs, seen)), k) == CatalogUnion.cu_bump(hit, CatalogUnion.cu_times(CatalogUnion.cu_keys(rest), k)) : Nat}:
  match seen hit:
    case True{} True{}:
      +h1 = LA.pcu.has_at(bs, CU.Ent{ck, ca, cd, ct, cc, cf, ch}, k, True{}, es, eh)
      +h2 = LA.pcu.has_in(bs, k)
      LA.pcu.absurdF({CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra.go(CU.Ent{ck, ca, cd, ct, cc, cf, ch} <> rest, bs, True{})), k) == CatalogUnion.cu_bump(True{}, CatalogUnion.cu_times(CatalogUnion.cu_keys(rest), k)) : Nat}, Equal.trans(Bool, False{}, CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k), True{}, Equal.sym(Bool, CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k), False{}, hb), Equal.trans(Bool, CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k), CU.has(bs, k), True{}, Equal.sym(Bool, CU.has(bs, k), CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k), h2), h1)))
    case True{} False{}:
      ih
    case False{} True{}:
      %Equal.sym(Bool, Nat.is_eq(ck, k), True{}, eh) : {CatalogUnion.cu_bump(_, CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra(rest, bs)), k)) == CatalogUnion.cu_bump(True{}, CatalogUnion.cu_times(CatalogUnion.cu_keys(rest), k)) : Nat}
      %Equal.sym(Nat, CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra(rest, bs)), k), CatalogUnion.cu_times(CatalogUnion.cu_keys(rest), k), ih) : {CatalogUnion.cu_bump(True{}, _) == CatalogUnion.cu_bump(True{}, CatalogUnion.cu_times(CatalogUnion.cu_keys(rest), k)) : Nat}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_eq(ck, k), False{}, eh) : {CatalogUnion.cu_bump(_, CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra(rest, bs)), k)) == CatalogUnion.cu_times(CatalogUnion.cu_keys(rest), k) : Nat}
      ih

def puo.tail(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, +k: Nat, +hb: {CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k) == False{} : Bool}) -> {CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra(cs, bs)), k) == CatalogUnion.cu_times(CatalogUnion.cu_keys(cs), k) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case c <> +rest:
      match c:
        case CU.Ent{+ck, +ca, +cd, +ct, +cc, +cf, +ch}:
          puo.go(CU.has(bs, ck), Nat.is_eq(ck, k), ck, ca, cd, ct, cc, cf, ch, rest, bs, k, {==}, {==}, hb, puo.tail(rest, bs, k, hb))

def puo.main(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, hb: {CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k) == False{} : Bool}) -> {CatalogUnion.cu_times(CatalogUnion.cu_keys(List.drop(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs))), k) == CatalogUnion.cu_times(CatalogUnion.cu_keys(cs), k) : Nat}:
  %Equal.sym(List<&2, CU.Ent>, List.drop(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs)), CU.extra(cs, bs), LA.pcu.drop_bundled(bs, cs, CU.extra(cs, bs))) : {CatalogUnion.cu_times(CatalogUnion.cu_keys(_), k) == CatalogUnion.cu_times(CatalogUnion.cu_keys(cs), k) : Nat}
  puo.tail(cs, bs, k, hb)

def CatalogUnion.union_tail_keeps_compiled_only(bs, cs, k, hb):
  puo.main(bs, cs, k, hb)
