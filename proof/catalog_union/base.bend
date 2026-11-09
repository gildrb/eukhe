# eukhe: lemmas the proofs of area catalog_union share

import Base
import ../../bend/catalog_union.bend as CU
import ../../laws/catalog_union.bend as CatalogUnion

# ---- catalog_union ----

# proof_catalog_union: the catalog union laws (LAWS.bend section catalog_union,
# C1), about bend/catalog_union.bend.
#
# One lemma carries them all (`pcu.find_union`): the lookup of a key in
# the union is `pick` of its lookups in the two sources. The bundled part
# answers `pick.b` (`pcu.find_bundled`: a bundled entry keeps its key, so
# its compiled twin is the twin at the key looked up); the compiled part
# answers its lookup unless the bundle has the key (`pcu.find_extra`); an
# append answers the first lookup that hits (`pcu.find_app`). Each law then
# reads `pick` at the lookups it assumes. The count of a key follows the
# same three steps (`pcu.count_app`, `pcu.count_bundled`,
# `pcu.count_extra`): the union lists a key as often as the bundle, or,
# when the bundle lacks it, as often as the compiled catalog.

# Logic
# -----

def pcu.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pcu.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pcu.BD(_, A, Unit)
  Unit{}

def pcu.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pcu.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pcu.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, pcu.eq_true(p, q, h))

# What the union answers
# ----------------------

# the bundled part's answer: a bundled entry with its compiled twin
def pcu.pick.b(mb: Maybe<&2, CU.Ent>, +mc: Maybe<&2, CU.Ent>) -> Maybe<&2, CU.Ent>:
  match mb:
    case None{}:
      None{}
    case Some{b}:
      Some{CU.with(b, mc)}

# the compiled part's answer: none when the bundle has the key
def pcu.gate(h: Bool, m: Maybe<&2, CU.Ent>) -> Maybe<&2, CU.Ent>:
  match h:
    case True{}:
      None{}
    case False{}:
      m

# the union's answer
def pcu.pick(mb: Maybe<&2, CU.Ent>, +mc: Maybe<&2, CU.Ent>) -> Maybe<&2, CU.Ent>:
  match mb:
    case None{}:
      mc
    case Some{b}:
      Some{CU.with(b, mc)}

# Lookup
# ------

def pcu.find_app.go(hit: Bool, +e: CU.Ent, +rest: List<&2, CU.Ent>, +ys: List<&2, CU.Ent>, +k: Nat, ih: {CU.find(List.append(&2, CU.Ent, rest, ys), k) == Maybe.or(&2, CU.Ent, CU.find(rest, k), CU.find(ys, k)) : Maybe<&2, CU.Ent>}) -> {CU.find.go(e <> List.append(&2, CU.Ent, rest, ys), k, hit) == Maybe.or(&2, CU.Ent, CU.find.go(e <> rest, k, hit), CU.find(ys, k)) : Maybe<&2, CU.Ent>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih

# a lookup in xs ++ ys is the lookup in xs, else in ys
def pcu.find_app(xs: List<&2, CU.Ent>, +ys: List<&2, CU.Ent>, +k: Nat) -> {CU.find(List.append(&2, CU.Ent, xs, ys), k) == Maybe.or(&2, CU.Ent, CU.find(xs, k), CU.find(ys, k)) : Maybe<&2, CU.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case +e <> +rest:
      pcu.find_app.go(Nat.is_eq(CU.Ent.key(e), k), e, rest, ys, k, pcu.find_app(rest, ys, k))

# a bundled entry with its twin keeps its key
def pcu.key_with(b: CU.Ent, m: Maybe<&2, CU.Ent>) -> {CU.Ent.key(CU.with(b, m)) == CU.Ent.key(b) : Nat}:
  match b:
    case CU.Ent{bk, ba, bd, bt, bc, bf, bh}:
      match m:
        case None{}:
          {==}
        case Some{c}:
          match c:
            case CU.Ent{ck, ca, cd, ct, cc, cf, ch}:
              {==}

# The bundled part
# ----------------

def pcu.find_bundled.go(hit: Bool, +b: CU.Ent, +rest: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, eq: {Nat.is_eq(CU.Ent.key(b), k) == hit : Bool}, ih: {CU.find(CU.bundled(rest, cs), k) == pcu.pick.b(CU.find(rest, k), CU.find(cs, k)) : Maybe<&2, CU.Ent>}) -> {CU.find.go(CU.with(b, CU.find(cs, CU.Ent.key(b))) <> CU.bundled(rest, cs), k, hit) == pcu.pick.b(CU.find.go(b <> rest, k, hit), CU.find(cs, k)) : Maybe<&2, CU.Ent>}:
  match hit:
    case True{}:
      +same = pcu.eq_true(CU.Ent.key(b), k, eq)
      %same : {Some{CU.with(b, CU.find(cs, CU.Ent.key(b)))} == Some{CU.with(b, CU.find(cs, _))} : Maybe<&2, CU.Ent>}
      {==}
    case False{}:
      ih

# a lookup in the bundled part: the bundled entry with its compiled twin
def pcu.find_bundled(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat) -> {CU.find(CU.bundled(bs, cs), k) == pcu.pick.b(CU.find(bs, k), CU.find(cs, k)) : Maybe<&2, CU.Ent>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      +kw = Equal.sym(Nat, CU.Ent.key(CU.with(b, CU.find(cs, CU.Ent.key(b)))), CU.Ent.key(b), pcu.key_with(b, CU.find(cs, CU.Ent.key(b))))
      %kw : {CU.find.go(CU.with(b, CU.find(cs, CU.Ent.key(b))) <> CU.bundled(rest, cs), k, Nat.is_eq(_, k)) == pcu.pick.b(CU.find(b <> rest, k), CU.find(cs, k)) : Maybe<&2, CU.Ent>}
      pcu.find_bundled.go(Nat.is_eq(CU.Ent.key(b), k), b, rest, cs, k, {==}, pcu.find_bundled(rest, cs, k))

# The compiled part
# -----------------

def pcu.gate_none(h: Bool) -> {pcu.gate(h, None{}) == None{} : Maybe<&2, CU.Ent>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# a hit on c: the bundle has k exactly when it has c's key
def pcu.has_at(+bs: List<&2, CU.Ent>, +c: CU.Ent, +k: Nat, +seen: Bool, es: {CU.has(bs, CU.Ent.key(c)) == seen : Bool}, eh: {Nat.is_eq(CU.Ent.key(c), k) == True{} : Bool}) -> {CU.has(bs, k) == seen : Bool}:
  +same = pcu.eq_true(CU.Ent.key(c), k, eh)
  %same : {CU.has(bs, _) == seen : Bool}
  es

def pcu.find_extra.go(seen: Bool, hit: Bool, +c: CU.Ent, +rest: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, +k: Nat, es: {CU.has(bs, CU.Ent.key(c)) == seen : Bool}, +eh: {Nat.is_eq(CU.Ent.key(c), k) == hit : Bool}, ih: {CU.find(CU.extra(rest, bs), k) == pcu.gate(CU.has(bs, k), CU.find(rest, k)) : Maybe<&2, CU.Ent>}) -> {CU.find(CU.extra.go(c <> rest, bs, seen), k) == pcu.gate(CU.has(bs, k), CU.find.go(c <> rest, k, hit)) : Maybe<&2, CU.Ent>}:
  match seen hit:
    case True{} True{}:
      +hk = Equal.sym(Bool, CU.has(bs, k), True{}, pcu.has_at(bs, c, k, True{}, es, eh))
      %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.extra(rest, bs), k), pcu.gate(CU.has(bs, k), CU.find(rest, k)), ih) : {_ == pcu.gate(CU.has(bs, k), Some{c}) : Maybe<&2, CU.Ent>}
      %hk : {pcu.gate(_, CU.find(rest, k)) == pcu.gate(_, Some{c}) : Maybe<&2, CU.Ent>}
      {==}
    case True{} False{}:
      ih
    case False{} True{}:
      +hk = Equal.sym(Bool, CU.has(bs, k), False{}, pcu.has_at(bs, c, k, False{}, es, eh))
      %hk : {CU.find.go(c <> CU.extra(rest, bs), k, Nat.is_eq(CU.Ent.key(c), k)) == pcu.gate(_, Some{c}) : Maybe<&2, CU.Ent>}
      %Equal.sym(Bool, Nat.is_eq(CU.Ent.key(c), k), True{}, eh) : {CU.find.go(c <> CU.extra(rest, bs), k, _) == Some{c} : Maybe<&2, CU.Ent>}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_eq(CU.Ent.key(c), k), False{}, eh) : {CU.find.go(c <> CU.extra(rest, bs), k, _) == pcu.gate(CU.has(bs, k), CU.find(rest, k)) : Maybe<&2, CU.Ent>}
      ih

# a lookup in the compiled part: the compiled entry, unless the bundle
# has the key
def pcu.find_extra(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, +k: Nat) -> {CU.find(CU.extra(cs, bs), k) == pcu.gate(CU.has(bs, k), CU.find(cs, k)) : Maybe<&2, CU.Ent>}:
  match cs:
    case Nil{}:
      Equal.sym(Maybe<&2, CU.Ent>, pcu.gate(CU.has(bs, k), None{}), None{}, pcu.gate_none(CU.has(bs, k)))
    case +c <> +rest:
      pcu.find_extra.go(CU.has(bs, CU.Ent.key(c)), Nat.is_eq(CU.Ent.key(c), k), c, rest, bs, k, {==}, {==}, pcu.find_extra(rest, bs, k))

# The union
# ---------

def pcu.or_pick(m: Maybe<&2, CU.Ent>, +mc: Maybe<&2, CU.Ent>) -> {Maybe.or(&2, CU.Ent, pcu.pick.b(m, mc), pcu.gate(Maybe.is_some(&2, CU.Ent, m), mc)) == pcu.pick(m, mc) : Maybe<&2, CU.Ent>}:
  match m:
    case None{}:
      {==}
    case Some{b}:
      {==}

# a lookup in the union is pick of the lookups in the two sources
def pcu.find_union(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat) -> {CU.find(CU.union(bs, cs), k) == pcu.pick(CU.find(bs, k), CU.find(cs, k)) : Maybe<&2, CU.Ent>}:
  +app = pcu.find_app(CU.bundled(bs, cs), CU.extra(cs, bs), k)
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(bs, cs), k), Maybe.or(&2, CU.Ent, CU.find(CU.bundled(bs, cs), k), CU.find(CU.extra(cs, bs), k)), app) : {_ == pcu.pick(CU.find(bs, k), CU.find(cs, k)) : Maybe<&2, CU.Ent>}
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.bundled(bs, cs), k), pcu.pick.b(CU.find(bs, k), CU.find(cs, k)), pcu.find_bundled(bs, cs, k)) : {Maybe.or(&2, CU.Ent, _, CU.find(CU.extra(cs, bs), k)) == pcu.pick(CU.find(bs, k), CU.find(cs, k)) : Maybe<&2, CU.Ent>}
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.extra(cs, bs), k), pcu.gate(CU.has(bs, k), CU.find(cs, k)), pcu.find_extra(cs, bs, k)) : {Maybe.or(&2, CU.Ent, pcu.pick.b(CU.find(bs, k), CU.find(cs, k)), _) == pcu.pick(CU.find(bs, k), CU.find(cs, k)) : Maybe<&2, CU.Ent>}
  pcu.or_pick(CU.find(bs, k), CU.find(cs, k))

# the union at k from the lookups at k
def pcu.at(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +mb: Maybe<&2, CU.Ent>, +mc: Maybe<&2, CU.Ent>, hb: {CU.find(bs, k) == mb : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == mc : Maybe<&2, CU.Ent>}) -> {CU.find(CU.union(bs, cs), k) == pcu.pick(mb, mc) : Maybe<&2, CU.Ent>}:
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(bs, cs), k), pcu.pick(CU.find(bs, k), CU.find(cs, k)), pcu.find_union(bs, cs, k)) : {_ == pcu.pick(mb, mc) : Maybe<&2, CU.Ent>}
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(bs, k), mb, hb) : {pcu.pick(_, CU.find(cs, k)) == pcu.pick(mb, mc) : Maybe<&2, CU.Ent>}
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(cs, k), mc, hc) : {pcu.pick(mb, _) == pcu.pick(mb, mc) : Maybe<&2, CU.Ent>}
  {==}

# a merged entry as field f shows it: the bundled key, api and data, and
# the field filled by the rule
def pcu.merge_slot(+b: CU.Ent, +c: CU.Ent, +f: CU.Fld) -> {CU.Ent.slot(CU.merge(b, c), f) == CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(CU.Ent.opt(b, f), CU.Ent.opt(c, f), Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)))} : CU.Slot}:
  match b c:
    case CU.Ent{bk, ba, bd, bt, bc, bf, bh} CU.Ent{ck, ca, cd, ct, cc, cf, ch}:
      match f:
        case CU.Tlm{}:
          {==}
        case CU.Compat{}:
          {==}
        case CU.Featured{}:
          {==}
        case CU.Headers{}:
          {==}

# a model in both sources, as field f shows it
def pcu.both(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +b: CU.Ent, +c: CU.Ent, +f: CU.Fld, hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}) -> {CU.slot(CU.find(CU.union(bs, cs), k), f) == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(CU.Ent.opt(b, f), CU.Ent.opt(c, f), Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)))}} : Maybe<&2, CU.Slot>}:
  +u = pcu.at(bs, cs, k, Some{b}, Some{c}, hb, hc)
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(bs, cs), k), Some{CU.merge(b, c)}, u) : {CU.slot(_, f) == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(CU.Ent.opt(b, f), CU.Ent.opt(c, f), Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)))}} : Maybe<&2, CU.Slot>}
  %Equal.sym(CU.Slot, CU.Ent.slot(CU.merge(b, c), f), CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(CU.Ent.opt(b, f), CU.Ent.opt(c, f), Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)))}, pcu.merge_slot(b, c, f)) : {Some{_} == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.fill(CU.Ent.opt(b, f), CU.Ent.opt(c, f), Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)))}} : Maybe<&2, CU.Slot>}
  {==}

# The list, place by place
# ------------------------
# The laws union_nil_*, union_head_is_bundle, union_tail_* and union_at_*
# read the union's list against the laws' constructor helpers
# (CatalogUnion.cu_keys, cu_kad, cu_in, cu_times): the bundled part has
# one entry per bundled entry, in order, so the union cut at the bundle's
# length is the bundled part and the compiled part (`pcu.take_bundled`,
# `pcu.drop_bundled`), and its entry at a bundled entry's place is that
# entry with its twin (`pcu.get_bundled`); the bundle has a key exactly
# when its keys hold it (`pcu.has_in`); the first entry with a key is the
# lookup's twin (`pcu.find_first`).

def pcu.is_eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pcu.is_eq_refl(p)

def pcu.or_false_l(x: Bool, y: Bool, h: {Bool.or(x, y) == False{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      pcu.absurdF({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))

def pcu.or_false_r(x: Bool, y: Bool, h: {Bool.or(x, y) == False{} : Bool}) -> {y == False{} : Bool}:
  match x:
    case False{}:
      h
    case True{}:
      pcu.absurdF({y == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))

def pcu.take_zero(xs: List<&2, CU.Ent>) -> {List.take(&2, CU.Ent, xs, 0n) == Nil{} : List<&2, CU.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def pcu.drop_zero(xs: List<&2, CU.Ent>) -> {List.drop(&2, CU.Ent, xs, 0n) == xs : List<&2, CU.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

# the first entries of the bundled part then e, as many as the bundle
# has, are the bundled part
def pcu.take_bundled(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +e: List<&2, CU.Ent>) -> {List.take(&2, CU.Ent, List.append(&2, CU.Ent, CU.bundled(bs, cs), e), List.length(&2, CU.Ent, bs)) == CU.bundled(bs, cs) : List<&2, CU.Ent>}:
  match bs:
    case Nil{}:
      pcu.take_zero(e)
    case +b <> +rest:
      Equal.cong(List<&2, CU.Ent>, List<&2, CU.Ent>, z => CU.with(b, CU.find(cs, CU.Ent.key(b))) <> z, List.take(&2, CU.Ent, List.append(&2, CU.Ent, CU.bundled(rest, cs), e), List.length(&2, CU.Ent, rest)), CU.bundled(rest, cs), pcu.take_bundled(rest, cs, e))

# and the entries after them are e
def pcu.drop_bundled(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +e: List<&2, CU.Ent>) -> {List.drop(&2, CU.Ent, List.append(&2, CU.Ent, CU.bundled(bs, cs), e), List.length(&2, CU.Ent, bs)) == e : List<&2, CU.Ent>}:
  match bs:
    case Nil{}:
      pcu.drop_zero(e)
    case b <> rest:
      pcu.drop_bundled(rest, cs, e)

# the entry at the place of b in the bundled part (then e) is b with its
# twin
def pcu.get_bundled(xs: List<&2, CU.Ent>, +b: CU.Ent, +ys: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +e: List<&2, CU.Ent>) -> {List.get(&2, CU.Ent, List.append(&2, CU.Ent, CU.bundled(List.append(&2, CU.Ent, xs, b <> ys), cs), e), List.length(&2, CU.Ent, xs)) == Some{CU.with(b, CU.find(cs, CU.Ent.key(b)))} : Maybe<&2, CU.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      pcu.get_bundled(rest, b, ys, cs, e)

def pcu.has_in.go(hit: Bool, +e: CU.Ent, +rest: List<&2, CU.Ent>, +k: Nat, ih: {CU.has(rest, k) == CatalogUnion.cu_in(CatalogUnion.cu_keys(rest), k) : Bool}) -> {Maybe.is_some(&2, CU.Ent, CU.find.go(e <> rest, k, hit)) == Bool.or(hit, CatalogUnion.cu_in(CatalogUnion.cu_keys(rest), k)) : Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih

# the bundle has a key exactly when its keys hold it
def pcu.has_in(bs: List<&2, CU.Ent>, +k: Nat) -> {CU.has(bs, k) == CatalogUnion.cu_in(CatalogUnion.cu_keys(bs), k) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case CU.Ent{+bk, +ba, +bd, +bt, +bc, +bf, +bh}:
          pcu.has_in.go(Nat.is_eq(bk, k), CU.Ent{bk, ba, bd, bt, bc, bf, bh}, rest, k, pcu.has_in(rest, k))

# c has key k and no entry of cp does: the lookup in cp, c, cq finds c
def pcu.find_first(cp: List<&2, CU.Ent>, +c: CU.Ent, +cq: List<&2, CU.Ent>, +k: Nat, +hc: {Nat.is_eq(CU.Ent.key(c), k) == True{} : Bool}, +h: {CatalogUnion.cu_in(CatalogUnion.cu_keys(cp), k) == False{} : Bool}) -> {CU.find(List.append(&2, CU.Ent, cp, c <> cq), k) == Some{c} : Maybe<&2, CU.Ent>}:
  match cp:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(CU.Ent.key(c), k), True{}, hc) : {CU.find.go(c <> cq, k, _) == Some{c} : Maybe<&2, CU.Ent>}
      {==}
    case e <> +rest:
      match e:
        case CU.Ent{+ek, +ea, +ed, +et, +ec, +ef, +eh}:
          +hx = pcu.or_false_l(Nat.is_eq(ek, k), CatalogUnion.cu_in(CatalogUnion.cu_keys(rest), k), h)
          +hr = pcu.or_false_r(Nat.is_eq(ek, k), CatalogUnion.cu_in(CatalogUnion.cu_keys(rest), k), h)
          %Equal.sym(Bool, Nat.is_eq(ek, k), False{}, hx) : {CU.find.go(CU.Ent{ek, ea, ed, et, ec, ef, eh} <> List.append(&2, CU.Ent, rest, c <> cq), k, _) == Some{c} : Maybe<&2, CU.Ent>}
          pcu.find_first(rest, c, cq, k, hc, hr)

# a bundled entry at its place, its twin the first compiled entry with
# its key: the bundled entry merged with that twin
def pcu.at_twin(+bp: List<&2, CU.Ent>, +bq: List<&2, CU.Ent>, +cp: List<&2, CU.Ent>, +cq: List<&2, CU.Ent>, +k: Nat, +a: Nat, +d: Nat, +t: Maybe<&2, Nat>, +cm: Maybe<&2, Nat>, +ft: Maybe<&2, Nat>, +hd: Maybe<&2, Nat>, +ca: Nat, +cd: Nat, +ct: Maybe<&2, Nat>, +cc: Maybe<&2, Nat>, +cf: Maybe<&2, Nat>, +ch: Maybe<&2, Nat>, hp: {CatalogUnion.cu_in(CatalogUnion.cu_keys(cp), k) == False{} : Bool}) -> {List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)) == Some{CU.merge(CU.Ent{k, a, d, t, cm, ft, hd}, CU.Ent{k, ca, cd, ct, cc, cf, ch})} : Maybe<&2, CU.Ent>}:
  +g = pcu.get_bundled(bp, CU.Ent{k, a, d, t, cm, ft, hd}, bq, List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq), CU.extra(List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq), List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq)))
  %Equal.sym(Maybe<&2, CU.Ent>, List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)), Some{CU.with(CU.Ent{k, a, d, t, cm, ft, hd}, CU.find(List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq), k))}, g) : {_ == Some{CU.merge(CU.Ent{k, a, d, t, cm, ft, hd}, CU.Ent{k, ca, cd, ct, cc, cf, ch})} : Maybe<&2, CU.Ent>}
  +tw = pcu.find_first(cp, CU.Ent{k, ca, cd, ct, cc, cf, ch}, cq, k, pcu.is_eq_refl(k), hp)
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq), k), Some{CU.Ent{k, ca, cd, ct, cc, cf, ch}}, tw) : {Some{CU.with(CU.Ent{k, a, d, t, cm, ft, hd}, _)} == Some{CU.merge(CU.Ent{k, a, d, t, cm, ft, hd}, CU.Ent{k, ca, cd, ct, cc, cf, ch})} : Maybe<&2, CU.Ent>}
  {==}
