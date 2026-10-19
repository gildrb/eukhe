# proof_catalog_union: the catalog union laws (laws/catalog_union.bend,
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

import Base
import ./catalog_union.bend as CU

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

def pcu.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pcu.BD(_, Unit, A)
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
    case CU.Ent{bk, ba, bd, bo}:
      match m:
        case None{}:
          {==}
        case Some{c}:
          match c:
            case CU.Ent{ck, ca, cd, co}:
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

# The laws
# --------

def pcu.some_pick(mb: Maybe<&2, CU.Ent>, +mc: Maybe<&2, CU.Ent>) -> {Maybe.is_some(&2, CU.Ent, pcu.pick(mb, mc)) == Bool.or(Maybe.is_some(&2, CU.Ent, mb), Maybe.is_some(&2, CU.Ent, mc)) : Bool}:
  match mb:
    case None{}:
      {==}
    case Some{b}:
      {==}

def pcu.hides_nothing(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat) -> {CU.has(CU.union(bs, cs), k) == Bool.or(CU.has(bs, k), CU.has(cs, k)) : Bool}:
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(bs, cs), k), pcu.pick(CU.find(bs, k), CU.find(cs, k)), pcu.find_union(bs, cs, k)) : {Maybe.is_some(&2, CU.Ent, _) == Bool.or(CU.has(bs, k), CU.has(cs, k)) : Bool}
  pcu.some_pick(CU.find(bs, k), CU.find(cs, k))

# the union at k from the lookups at k
def pcu.at(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +mb: Maybe<&2, CU.Ent>, +mc: Maybe<&2, CU.Ent>, hb: {CU.find(bs, k) == mb : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == mc : Maybe<&2, CU.Ent>}) -> {CU.find(CU.union(bs, cs), k) == pcu.pick(mb, mc) : Maybe<&2, CU.Ent>}:
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(bs, cs), k), pcu.pick(CU.find(bs, k), CU.find(cs, k)), pcu.find_union(bs, cs, k)) : {_ == pcu.pick(mb, mc) : Maybe<&2, CU.Ent>}
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(bs, k), mb, hb) : {pcu.pick(_, CU.find(cs, k)) == pcu.pick(mb, mc) : Maybe<&2, CU.Ent>}
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(cs, k), mc, hc) : {pcu.pick(mb, _) == pcu.pick(mb, mc) : Maybe<&2, CU.Ent>}
  {==}

def pcu.bundled_only(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +b: CU.Ent, hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == None{} : Maybe<&2, CU.Ent>}) -> {CU.find(CU.union(bs, cs), k) == Some{b} : Maybe<&2, CU.Ent>}:
  pcu.at(bs, cs, k, Some{b}, None{}, hb, hc)

def pcu.compiled_only(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +c: CU.Ent, hb: {CU.find(bs, k) == None{} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}) -> {CU.find(CU.union(bs, cs), k) == Some{c} : Maybe<&2, CU.Ent>}:
  pcu.at(bs, cs, k, None{}, Some{c}, hb, hc)

def pcu.both_keeps_bundled(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +b: CU.Ent, +c: CU.Ent, +v: Nat, hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}, hv: {CU.Ent.opt(b) == Some{v} : Maybe<&2, Nat>}) -> {CU.find(CU.union(bs, cs), k) == Some{CU.Ent{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), Some{v}}} : Maybe<&2, CU.Ent>}:
  match b c:
    case CU.Ent{+bk, +ba, +bd, +bo} CU.Ent{+ck, +ca, +cd, +co}:
      +u = pcu.at(bs, cs, k, Some{CU.Ent{bk, ba, bd, bo}}, Some{CU.Ent{ck, ca, cd, co}}, hb, hc)
      %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(bs, cs), k), Some{CU.Ent{bk, ba, bd, CU.fill(bo, co, Nat.is_eq(ba, ca))}}, u) : {_ == Some{CU.Ent{bk, ba, bd, Some{v}}} : Maybe<&2, CU.Ent>}
      %Equal.sym(Maybe<&2, Nat>, bo, Some{v}, hv) : {Some{CU.Ent{bk, ba, bd, CU.fill(_, co, Nat.is_eq(ba, ca))}} == Some{CU.Ent{bk, ba, bd, Some{v}}} : Maybe<&2, CU.Ent>}
      {==}

def pcu.both_fills(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +b: CU.Ent, +c: CU.Ent, hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}, hn: {CU.Ent.opt(b) == None{} : Maybe<&2, Nat>}, ha: {Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)) == True{} : Bool}) -> {CU.find(CU.union(bs, cs), k) == Some{CU.Ent{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.Ent.opt(c)}} : Maybe<&2, CU.Ent>}:
  match b c:
    case CU.Ent{+bk, +ba, +bd, +bo} CU.Ent{+ck, +ca, +cd, +co}:
      +u = pcu.at(bs, cs, k, Some{CU.Ent{bk, ba, bd, bo}}, Some{CU.Ent{ck, ca, cd, co}}, hb, hc)
      %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(bs, cs), k), Some{CU.Ent{bk, ba, bd, CU.fill(bo, co, Nat.is_eq(ba, ca))}}, u) : {_ == Some{CU.Ent{bk, ba, bd, co}} : Maybe<&2, CU.Ent>}
      %Equal.sym(Maybe<&2, Nat>, bo, None{}, hn) : {Some{CU.Ent{bk, ba, bd, CU.fill(_, co, Nat.is_eq(ba, ca))}} == Some{CU.Ent{bk, ba, bd, co}} : Maybe<&2, CU.Ent>}
      %Equal.sym(Bool, Nat.is_eq(ba, ca), True{}, ha) : {Some{CU.Ent{bk, ba, bd, CU.fill(None{}, co, _)}} == Some{CU.Ent{bk, ba, bd, co}} : Maybe<&2, CU.Ent>}
      {==}

def pcu.both_other_api(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, +b: CU.Ent, +c: CU.Ent, hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}, hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}, hn: {CU.Ent.opt(b) == None{} : Maybe<&2, Nat>}, ha: {Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)) == False{} : Bool}) -> {CU.find(CU.union(bs, cs), k) == Some{CU.Ent{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), None{}}} : Maybe<&2, CU.Ent>}:
  match b c:
    case CU.Ent{+bk, +ba, +bd, +bo} CU.Ent{+ck, +ca, +cd, +co}:
      +u = pcu.at(bs, cs, k, Some{CU.Ent{bk, ba, bd, bo}}, Some{CU.Ent{ck, ca, cd, co}}, hb, hc)
      %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(bs, cs), k), Some{CU.Ent{bk, ba, bd, CU.fill(bo, co, Nat.is_eq(ba, ca))}}, u) : {_ == Some{CU.Ent{bk, ba, bd, None{}}} : Maybe<&2, CU.Ent>}
      %Equal.sym(Maybe<&2, Nat>, bo, None{}, hn) : {Some{CU.Ent{bk, ba, bd, CU.fill(_, co, Nat.is_eq(ba, ca))}} == Some{CU.Ent{bk, ba, bd, None{}}} : Maybe<&2, CU.Ent>}
      %Equal.sym(Bool, Nat.is_eq(ba, ca), False{}, ha) : {Some{CU.Ent{bk, ba, bd, CU.fill(None{}, co, _)}} == Some{CU.Ent{bk, ba, bd, None{}}} : Maybe<&2, CU.Ent>}
      {==}

def pcu.order_free(+k: Nat, +xs: List<&2, CU.Ent>, +xs2: List<&2, CU.Ent>, +ys: List<&2, CU.Ent>, +ys2: List<&2, CU.Ent>, sx: {CU.find(xs, k) == CU.find(xs2, k) : Maybe<&2, CU.Ent>}, sy: {CU.find(ys, k) == CU.find(ys2, k) : Maybe<&2, CU.Ent>}) -> {CU.find(CU.read(CU.Cat{CU.Bundled{}, xs}, CU.Cat{CU.Compiled{}, ys}), k) == CU.find(CU.read(CU.Cat{CU.Compiled{}, ys2}, CU.Cat{CU.Bundled{}, xs2}), k) : Maybe<&2, CU.Ent>}:
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(xs, ys), k), pcu.pick(CU.find(xs, k), CU.find(ys, k)), pcu.find_union(xs, ys, k)) : {_ == CU.find(CU.union(xs2, ys2), k) : Maybe<&2, CU.Ent>}
  Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(xs2, ys2), k), pcu.pick(CU.find(xs, k), CU.find(ys, k)), pcu.at(xs2, ys2, k, CU.find(xs, k), CU.find(ys, k), Equal.sym(Maybe<&2, CU.Ent>, CU.find(xs, k), CU.find(xs2, k), sx), Equal.sym(Maybe<&2, CU.Ent>, CU.find(ys, k), CU.find(ys2, k), sy)))

# One model list
# --------------

def pcu.count_app.go(hit: Bool, +e: CU.Ent, +rest: List<&2, CU.Ent>, +ys: List<&2, CU.Ent>, +k: Nat, ih: {CU.count(List.append(&2, CU.Ent, rest, ys), k) == Nat.add(CU.count(rest, k), CU.count(ys, k)) : Nat}) -> {CU.count.go(e <> List.append(&2, CU.Ent, rest, ys), k, hit) == Nat.add(CU.count.go(e <> rest, k, hit), CU.count(ys, k)) : Nat}:
  match hit:
    case True{}:
      Equal.cong(Nat, Nat, x => 1n+x, CU.count(List.append(&2, CU.Ent, rest, ys), k), Nat.add(CU.count(rest, k), CU.count(ys, k)), ih)
    case False{}:
      ih

# the count in xs ++ ys is the count in xs plus the count in ys
def pcu.count_app(xs: List<&2, CU.Ent>, +ys: List<&2, CU.Ent>, +k: Nat) -> {CU.count(List.append(&2, CU.Ent, xs, ys), k) == Nat.add(CU.count(xs, k), CU.count(ys, k)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +e <> +rest:
      pcu.count_app.go(Nat.is_eq(CU.Ent.key(e), k), e, rest, ys, k, pcu.count_app(rest, ys, k))

def pcu.count_bundled.go(hit: Bool, +b: CU.Ent, +rest: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, ih: {CU.count(CU.bundled(rest, cs), k) == CU.count(rest, k) : Nat}) -> {CU.count.go(CU.with(b, CU.find(cs, CU.Ent.key(b))) <> CU.bundled(rest, cs), k, hit) == CU.count.go(b <> rest, k, hit) : Nat}:
  match hit:
    case True{}:
      Equal.cong(Nat, Nat, x => 1n+x, CU.count(CU.bundled(rest, cs), k), CU.count(rest, k), ih)
    case False{}:
      ih

# the bundled part lists each key as often as the bundle
def pcu.count_bundled(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat) -> {CU.count(CU.bundled(bs, cs), k) == CU.count(bs, k) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      +kw = Equal.sym(Nat, CU.Ent.key(CU.with(b, CU.find(cs, CU.Ent.key(b)))), CU.Ent.key(b), pcu.key_with(b, CU.find(cs, CU.Ent.key(b))))
      %kw : {CU.count.go(CU.with(b, CU.find(cs, CU.Ent.key(b))) <> CU.bundled(rest, cs), k, Nat.is_eq(_, k)) == CU.count(b <> rest, k) : Nat}
      pcu.count_bundled.go(Nat.is_eq(CU.Ent.key(b), k), b, rest, cs, k, pcu.count_bundled(rest, cs, k))

# the compiled part's count: none when the bundle has the key
def pcu.gate_n(h: Bool, n: Nat) -> Nat:
  match h:
    case True{}:
      0n
    case False{}:
      n

def pcu.gate_n_zero(h: Bool) -> {pcu.gate_n(h, 0n) == 0n : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def pcu.count_extra.go(seen: Bool, hit: Bool, +c: CU.Ent, +rest: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, +k: Nat, es: {CU.has(bs, CU.Ent.key(c)) == seen : Bool}, +eh: {Nat.is_eq(CU.Ent.key(c), k) == hit : Bool}, ih: {CU.count(CU.extra(rest, bs), k) == pcu.gate_n(CU.has(bs, k), CU.count(rest, k)) : Nat}) -> {CU.count(CU.extra.go(c <> rest, bs, seen), k) == pcu.gate_n(CU.has(bs, k), CU.count.go(c <> rest, k, hit)) : Nat}:
  match seen hit:
    case True{} True{}:
      +hk = Equal.sym(Bool, CU.has(bs, k), True{}, pcu.has_at(bs, c, k, True{}, es, eh))
      %Equal.sym(Nat, CU.count(CU.extra(rest, bs), k), pcu.gate_n(CU.has(bs, k), CU.count(rest, k)), ih) : {_ == pcu.gate_n(CU.has(bs, k), 1n+CU.count(rest, k)) : Nat}
      %hk : {pcu.gate_n(_, CU.count(rest, k)) == pcu.gate_n(_, 1n+CU.count(rest, k)) : Nat}
      {==}
    case True{} False{}:
      ih
    case False{} True{}:
      +hk = Equal.sym(Bool, CU.has(bs, k), False{}, pcu.has_at(bs, c, k, False{}, es, eh))
      %Equal.sym(Bool, Nat.is_eq(CU.Ent.key(c), k), True{}, eh) : {CU.count.go(c <> CU.extra(rest, bs), k, _) == pcu.gate_n(CU.has(bs, k), 1n+CU.count(rest, k)) : Nat}
      %Equal.sym(Nat, CU.count(CU.extra(rest, bs), k), pcu.gate_n(CU.has(bs, k), CU.count(rest, k)), ih) : {1n+_ == pcu.gate_n(CU.has(bs, k), 1n+CU.count(rest, k)) : Nat}
      %hk : {1n+pcu.gate_n(_, CU.count(rest, k)) == pcu.gate_n(_, 1n+CU.count(rest, k)) : Nat}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_eq(CU.Ent.key(c), k), False{}, eh) : {CU.count.go(c <> CU.extra(rest, bs), k, _) == pcu.gate_n(CU.has(bs, k), CU.count(rest, k)) : Nat}
      ih

# the compiled part lists a key the bundle lacks as often as the compiled
# catalog, and a key the bundle has never
def pcu.count_extra(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>, +k: Nat) -> {CU.count(CU.extra(cs, bs), k) == pcu.gate_n(CU.has(bs, k), CU.count(cs, k)) : Nat}:
  match cs:
    case Nil{}:
      Equal.sym(Nat, pcu.gate_n(CU.has(bs, k), 0n), 0n, pcu.gate_n_zero(CU.has(bs, k)))
    case +c <> +rest:
      pcu.count_extra.go(CU.has(bs, CU.Ent.key(c)), Nat.is_eq(CU.Ent.key(c), k), c, rest, bs, k, {==}, {==}, pcu.count_extra(rest, bs, k))

# a key the list does not have, it lists never
def pcu.none_count.go(xs: List<&2, CU.Ent>, +k: Nat, hit: Bool, h: {Maybe.is_some(&2, CU.Ent, CU.find.go(xs, k, hit)) == False{} : Bool}) -> {CU.count.go(xs, k, hit) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case e <> +rest:
      match hit:
        case True{}:
          pcu.absurdT({CU.count.go(e <> rest, k, True{}) == 0n : Nat}, h)
        case False{}:
          pcu.none_count.go(rest, k, CU.key.at(rest, k), h)

def pcu.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, pcu.add_zero(p))

def pcu.once.go(hb: Bool, +bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, eb: {CU.has(bs, k) == hb : Bool}, ub: {Nat.is_le(CU.count(bs, k), 1n) == True{} : Bool}, uc: {Nat.is_le(CU.count(cs, k), 1n) == True{} : Bool}) -> {Nat.is_le(Nat.add(CU.count(bs, k), pcu.gate_n(hb, CU.count(cs, k))), 1n) == True{} : Bool}:
  match hb:
    case True{}:
      %Equal.sym(Nat, Nat.add(CU.count(bs, k), 0n), CU.count(bs, k), pcu.add_zero(CU.count(bs, k))) : {Nat.is_le(_, 1n) == True{} : Bool}
      ub
    case False{}:
      +z = pcu.none_count.go(bs, k, CU.key.at(bs, k), eb)
      %Equal.sym(Nat, CU.count(bs, k), 0n, z) : {Nat.is_le(Nat.add(_, CU.count(cs, k)), 1n) == True{} : Bool}
      uc

# when each source lists a key at most once, so does the union
def pcu.lists_once(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>, +k: Nat, ub: {Nat.is_le(CU.count(bs, k), 1n) == True{} : Bool}, uc: {Nat.is_le(CU.count(cs, k), 1n) == True{} : Bool}) -> {Nat.is_le(CU.count(CU.union(bs, cs), k), 1n) == True{} : Bool}:
  %Equal.sym(Nat, CU.count(CU.union(bs, cs), k), Nat.add(CU.count(CU.bundled(bs, cs), k), CU.count(CU.extra(cs, bs), k)), pcu.count_app(CU.bundled(bs, cs), CU.extra(cs, bs), k)) : {Nat.is_le(_, 1n) == True{} : Bool}
  %Equal.sym(Nat, CU.count(CU.bundled(bs, cs), k), CU.count(bs, k), pcu.count_bundled(bs, cs, k)) : {Nat.is_le(Nat.add(_, CU.count(CU.extra(cs, bs), k)), 1n) == True{} : Bool}
  %Equal.sym(Nat, CU.count(CU.extra(cs, bs), k), pcu.gate_n(CU.has(bs, k), CU.count(cs, k)), pcu.count_extra(cs, bs, k)) : {Nat.is_le(Nat.add(CU.count(bs, k), _), 1n) == True{} : Bool}
  pcu.once.go(CU.has(bs, k), bs, cs, k, {==}, ub, uc)
