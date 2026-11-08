# eukhe: the proof of LAW union_spec
#
# PROOF: the model's lookup is the spec's (us.find: key.at is the spec's
# key test, by the hit), its fill, merge and twin too (us.fill, us.merge,
# us.with), so the bundled part is the spec's (us.bundled); the bundle has
# a key exactly when the spec finds it (us.has), so the compiled-only part
# is the spec's (us.extra); the union appends the two.

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion

# Lookup
# ------

def us.key(e: CU.Ent) -> {CU.Ent.key(e) == CatalogUnion.cu_key(e) : Nat}:
  match e:
    case CU.Ent{k, a, d, t, c, f, h}:
      {==}

def us.go(hit: Bool, +e: CU.Ent, +rest: List<&2, CU.Ent>, +k: Nat, ih: {CU.find(rest, k) == CatalogUnion.cu_find(rest, k) : Maybe<&2, CU.Ent>}) -> {CU.find.go(e <> rest, k, hit) == CatalogUnion.cu_pick(hit, e, CatalogUnion.cu_find(rest, k)) : Maybe<&2, CU.Ent>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih

# the model's lookup is the spec's
def us.find(xs: List<&2, CU.Ent>, +k: Nat) -> {CU.find(xs, k) == CatalogUnion.cu_find(xs, k) : Maybe<&2, CU.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case CU.Ent{+ek, +ea, +ed, +et, +ec, +ef, +eh}:
          us.go(Nat.is_eq(ek, k), CU.Ent{ek, ea, ed, et, ec, ef, eh}, rest, k, us.find(rest, k))

# A model in both
# ---------------

def us.fill(o: Maybe<&2, Nat>, c: Maybe<&2, Nat>, same: Bool) -> {CU.fill(o, c, same) == CatalogUnion.cu_fill(o, c, same) : Maybe<&2, Nat>}:
  match o:
    case Some{v}:
      {==}
    case None{}:
      match same:
        case True{}:
          {==}
        case False{}:
          {==}

def us.merge(b: CU.Ent, c: CU.Ent) -> {CU.merge(b, c) == CatalogUnion.cu_merge(b, c) : CU.Ent}:
  match b c:
    case CU.Ent{bk, +ba, bd, +bt, +bc, +bf, +bh} CU.Ent{ck, +ca, cd, +ct, +cc, +cf, +ch}:
      %us.fill(bt, ct, Nat.is_eq(ba, ca)) : {CU.merge(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CU.Ent{ck, ca, cd, ct, cc, cf, ch}) == CU.Ent{bk, ba, bd, _, CatalogUnion.cu_fill(bc, cc, Nat.is_eq(ba, ca)), CatalogUnion.cu_fill(bf, cf, Nat.is_eq(ba, ca)), CatalogUnion.cu_fill(bh, ch, Nat.is_eq(ba, ca))} : CU.Ent}
      %us.fill(bc, cc, Nat.is_eq(ba, ca)) : {CU.merge(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CU.Ent{ck, ca, cd, ct, cc, cf, ch}) == CU.Ent{bk, ba, bd, CU.fill(bt, ct, Nat.is_eq(ba, ca)), _, CatalogUnion.cu_fill(bf, cf, Nat.is_eq(ba, ca)), CatalogUnion.cu_fill(bh, ch, Nat.is_eq(ba, ca))} : CU.Ent}
      %us.fill(bf, cf, Nat.is_eq(ba, ca)) : {CU.merge(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CU.Ent{ck, ca, cd, ct, cc, cf, ch}) == CU.Ent{bk, ba, bd, CU.fill(bt, ct, Nat.is_eq(ba, ca)), CU.fill(bc, cc, Nat.is_eq(ba, ca)), _, CatalogUnion.cu_fill(bh, ch, Nat.is_eq(ba, ca))} : CU.Ent}
      %us.fill(bh, ch, Nat.is_eq(ba, ca)) : {CU.merge(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CU.Ent{ck, ca, cd, ct, cc, cf, ch}) == CU.Ent{bk, ba, bd, CU.fill(bt, ct, Nat.is_eq(ba, ca)), CU.fill(bc, cc, Nat.is_eq(ba, ca)), CU.fill(bf, cf, Nat.is_eq(ba, ca)), _} : CU.Ent}
      {==}

def us.with(+b: CU.Ent, m: Maybe<&2, CU.Ent>) -> {CU.with(b, m) == CatalogUnion.cu_with(b, m) : CU.Ent}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      us.merge(b, c)

# The union
# ---------

def us.bundled(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> {CU.bundled(bs, cs) == CatalogUnion.cu_bundled(bs, cs) : List<&2, CU.Ent>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      %us.key(b) : {CU.bundled(b <> rest, cs) == CatalogUnion.cu_with(b, CatalogUnion.cu_find(cs, _)) <> CatalogUnion.cu_bundled(rest, cs) : List<&2, CU.Ent>}
      %us.find(cs, CU.Ent.key(b)) : {CU.bundled(b <> rest, cs) == CatalogUnion.cu_with(b, _) <> CatalogUnion.cu_bundled(rest, cs) : List<&2, CU.Ent>}
      %us.with(b, CU.find(cs, CU.Ent.key(b))) : {CU.bundled(b <> rest, cs) == _ <> CatalogUnion.cu_bundled(rest, cs) : List<&2, CU.Ent>}
      %us.bundled(rest, cs) : {CU.bundled(b <> rest, cs) == CU.with(b, CU.find(cs, CU.Ent.key(b))) <> _ : List<&2, CU.Ent>}
      {==}

# the bundle has a key exactly when the spec finds it there
def us.has(+bs: List<&2, CU.Ent>, +c: CU.Ent) -> {CU.has(bs, CU.Ent.key(c)) == Maybe.is_some(&2, CU.Ent, CatalogUnion.cu_find(bs, CatalogUnion.cu_key(c))) : Bool}:
  %us.key(c) : {CU.has(bs, CU.Ent.key(c)) == Maybe.is_some(&2, CU.Ent, CatalogUnion.cu_find(bs, _)) : Bool}
  %us.find(bs, CU.Ent.key(c)) : {CU.has(bs, CU.Ent.key(c)) == Maybe.is_some(&2, CU.Ent, _) : Bool}
  {==}

def us.keep(seen: Bool, +c: CU.Ent, +rest: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, ih: {CU.extra(rest, bs) == CatalogUnion.cu_extra(rest, bs) : List<&2, CU.Ent>}) -> {CU.extra.go(c <> rest, bs, seen) == CatalogUnion.cu_keep(seen, c, CatalogUnion.cu_extra(rest, bs)) : List<&2, CU.Ent>}:
  match seen:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, CU.Ent>, List<&2, CU.Ent>, z => c <> z, CU.extra(rest, bs), CatalogUnion.cu_extra(rest, bs), ih)

def us.extra(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>) -> {CU.extra(cs, bs) == CatalogUnion.cu_extra(cs, bs) : List<&2, CU.Ent>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      %us.has(bs, c) : {CU.extra(c <> rest, bs) == CatalogUnion.cu_keep(_, c, CatalogUnion.cu_extra(rest, bs)) : List<&2, CU.Ent>}
      us.keep(CU.has(bs, CU.Ent.key(c)), c, rest, bs, us.extra(rest, bs))

def CatalogUnion.union_spec(bs, cs):
  %us.bundled(bs, cs) : {CU.union(bs, cs) == List.append(&2, CU.Ent, _, CatalogUnion.cu_extra(cs, bs)) : List<&2, CU.Ent>}
  %us.extra(cs, bs) : {CU.union(bs, cs) == List.append(&2, CU.Ent, CU.bundled(bs, cs), _) : List<&2, CU.Ent>}
  {==}
