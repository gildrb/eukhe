# eukhe: the proof of LAW union_lists_each_model_once

import Base
import ../../bend/catalog_union.bend as CU
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pcu.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : LA.pcu.BD(_, Unit, A)
  Unit{}

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
      +kw = Equal.sym(Nat, CU.Ent.key(CU.with(b, CU.find(cs, CU.Ent.key(b)))), CU.Ent.key(b), LA.pcu.key_with(b, CU.find(cs, CU.Ent.key(b))))
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
      +hk = Equal.sym(Bool, CU.has(bs, k), True{}, LA.pcu.has_at(bs, c, k, True{}, es, eh))
      %Equal.sym(Nat, CU.count(CU.extra(rest, bs), k), pcu.gate_n(CU.has(bs, k), CU.count(rest, k)), ih) : {_ == pcu.gate_n(CU.has(bs, k), 1n+CU.count(rest, k)) : Nat}
      %hk : {pcu.gate_n(_, CU.count(rest, k)) == pcu.gate_n(_, 1n+CU.count(rest, k)) : Nat}
      {==}
    case True{} False{}:
      ih
    case False{} True{}:
      +hk = Equal.sym(Bool, CU.has(bs, k), False{}, LA.pcu.has_at(bs, c, k, False{}, es, eh))
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

def Laws.union_lists_each_model_once(bs, cs, k, ub, uc):
  pcu.lists_once(bs, cs, k, ub, uc)
