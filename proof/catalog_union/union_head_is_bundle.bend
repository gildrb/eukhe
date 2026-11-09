# eukhe: the proof of LAW union_head_is_bundle
#
# PROOF: the union cut at the bundle's length is the bundled part
# (pcu.take_bundled); an entry with its twin keeps the bundled key, api and
# data (puh.kad_with), entry by entry (puh.kad_bundled).

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion
import ./base.bend as LA

def puh.kad_with(m: Maybe<&2, CU.Ent>, +bk: Nat, +ba: Nat, +bd: Nat, +bt: Maybe<&2, Nat>, +bc: Maybe<&2, Nat>, +bf: Maybe<&2, Nat>, +bh: Maybe<&2, Nat>, +r: List<&2, CU.Ent>, +s: List<&2, CU.Ent>, ih: {CatalogUnion.cu_kad(r) == CatalogUnion.cu_kad(s) : List<&2, Nat>}) -> {CatalogUnion.cu_kad(CU.with(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, m) <> r) == bk <> ba <> bd <> CatalogUnion.cu_kad(s) : List<&2, Nat>}:
  match m:
    case None{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => bk <> ba <> bd <> z, CatalogUnion.cu_kad(r), CatalogUnion.cu_kad(s), ih)
    case Some{c}:
      match c:
        case CU.Ent{ck, ca, cd, ct, cc, cf, ch}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => bk <> ba <> bd <> z, CatalogUnion.cu_kad(r), CatalogUnion.cu_kad(s), ih)

def puh.kad_bundled(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> {CatalogUnion.cu_kad(CU.bundled(bs, cs)) == CatalogUnion.cu_kad(bs) : List<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case CU.Ent{+bk, +ba, +bd, +bt, +bc, +bf, +bh}:
          puh.kad_with(CU.find(cs, bk), bk, ba, bd, bt, bc, bf, bh, CU.bundled(rest, cs), rest, puh.kad_bundled(rest, cs))

def puh.main(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> {CatalogUnion.cu_kad(List.take(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs))) == CatalogUnion.cu_kad(bs) : List<&2, Nat>}:
  %Equal.sym(List<&2, CU.Ent>, List.take(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs)), CU.bundled(bs, cs), LA.pcu.take_bundled(bs, cs, CU.extra(cs, bs))) : {CatalogUnion.cu_kad(_) == CatalogUnion.cu_kad(bs) : List<&2, Nat>}
  puh.kad_bundled(bs, cs)

def CatalogUnion.union_head_is_bundle(bs, cs):
  puh.main(bs, cs)
