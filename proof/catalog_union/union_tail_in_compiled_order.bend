# eukhe: the proof of LAW union_tail_in_compiled_order
#
# PROOF: the union after the bundle's length is the compiled-only part
# (pcu.drop_bundled), which keeps each compiled entry exactly when the
# bundle lacks its key: the mask of those answers (put.mask, put.select).

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

# keep each compiled entry whose key the bundle lacks
def put.mask(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>) -> List<&2, Bool>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Bool.not(CU.has(bs, CU.Ent.key(c))) <> put.mask(rest, bs)

def put.go(seen: Bool, +c: CU.Ent, +rest: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, ih: {CatalogUnion.cu_select(put.mask(rest, bs), rest) == CU.extra(rest, bs) : List<&2, CU.Ent>}) -> {CatalogUnion.cu_sel(Bool.not(seen), c, CatalogUnion.cu_select(put.mask(rest, bs), rest)) == CU.extra.go(c <> rest, bs, seen) : List<&2, CU.Ent>}:
  match seen:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, CU.Ent>, List<&2, CU.Ent>, z => c <> z, CatalogUnion.cu_select(put.mask(rest, bs), rest), CU.extra(rest, bs), ih)

def put.select(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>) -> {CatalogUnion.cu_select(put.mask(cs, bs), cs) == CU.extra(cs, bs) : List<&2, CU.Ent>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      put.go(CU.has(bs, CU.Ent.key(c)), c, rest, bs, put.select(rest, bs))

def put.main(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> {CatalogUnion.cu_select(put.mask(cs, bs), cs) == List.drop(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs)) : List<&2, CU.Ent>}:
  %Equal.sym(List<&2, CU.Ent>, List.drop(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs)), CU.extra(cs, bs), LA.pcu.drop_bundled(bs, cs, CU.extra(cs, bs))) : {CatalogUnion.cu_select(put.mask(cs, bs), cs) == _ : List<&2, CU.Ent>}
  put.select(cs, bs)

def CatalogUnion.union_tail_in_compiled_order(bs, cs):
  (put.mask(cs, bs), put.main(bs, cs))
