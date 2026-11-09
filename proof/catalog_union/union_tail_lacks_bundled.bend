# eukhe: the proof of LAW union_tail_lacks_bundled
#
# PROOF: the union after the bundle's length is the compiled-only part
# (pcu.drop_bundled); a compiled entry it keeps has a key the bundle lacks
# (pcu.has_in), so not k, which the bundle has.

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

def pui.go(seen: Bool, hit: Bool, +ck: Nat, +ca: Nat, +cd: Nat, +ct: Maybe<&2, Nat>, +cc: Maybe<&2, Nat>, +cf: Maybe<&2, Nat>, +ch: Maybe<&2, Nat>, +rest: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, +k: Nat, es: {CU.has(bs, ck) == seen : Bool}, eh: {Nat.is_eq(ck, k) == hit : Bool}, hb: {CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k) == True{} : Bool}, ih: {CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra(rest, bs)), k) == 0n : Nat}) -> {CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra.go(CU.Ent{ck, ca, cd, ct, cc, cf, ch} <> rest, bs, seen)), k) == 0n : Nat}:
  match seen hit:
    case True{} True{}:
      ih
    case True{} False{}:
      ih
    case False{} True{}:
      +h1 = LA.pcu.has_at(bs, CU.Ent{ck, ca, cd, ct, cc, cf, ch}, k, False{}, es, eh)
      +h2 = LA.pcu.has_in(bs, k)
      LA.pcu.absurdF({CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra.go(CU.Ent{ck, ca, cd, ct, cc, cf, ch} <> rest, bs, False{})), k) == 0n : Nat}, Equal.trans(Bool, False{}, CU.has(bs, k), True{}, Equal.sym(Bool, CU.has(bs, k), False{}, h1), Equal.trans(Bool, CU.has(bs, k), CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k), True{}, h2, hb)))
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_eq(ck, k), False{}, eh) : {CatalogUnion.cu_bump(_, CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra(rest, bs)), k)) == 0n : Nat}
      ih

def pui.tail(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, +k: Nat, +hb: {CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k) == True{} : Bool}) -> {CatalogUnion.cu_times(CatalogUnion.cu_keys(CU.extra(cs, bs)), k) == 0n : Nat}:
  match cs:
    case Nil{}:
      {==}
    case c <> +rest:
      match c:
        case CU.Ent{+ck, +ca, +cd, +ct, +cc, +cf, +ch}:
          pui.go(CU.has(bs, ck), Nat.is_eq(ck, k), ck, ca, cd, ct, cc, cf, ch, rest, bs, k, {==}, {==}, hb, pui.tail(rest, bs, k, hb))

def pui.main(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, hb: {CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k) == True{} : Bool}) -> {CatalogUnion.cu_times(CatalogUnion.cu_keys(List.drop(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs))), k) == 0n : Nat}:
  %Equal.sym(List<&2, CU.Ent>, List.drop(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs)), CU.extra(cs, bs), LA.pcu.drop_bundled(bs, cs, CU.extra(cs, bs))) : {CatalogUnion.cu_times(CatalogUnion.cu_keys(_), k) == 0n : Nat}
  pui.tail(cs, bs, k, hb)

def CatalogUnion.union_tail_lacks_bundled(bs, cs, k, hb):
  pui.main(bs, cs, k, hb)
