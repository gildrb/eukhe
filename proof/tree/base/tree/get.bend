# eukhe: lemmas the proofs of area tree share: tree/get

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/logic/bool.bend as LLogicBool
import ../../../base/nat.bend as LNat
import ../../../base/tree.bend as LTree
import ../logic.bend as LALogic
import ../nat.bend as LANat
import ./above.bend as LATreeAbove
import ./dels.bend as LATreeDels

# Lookup
# ------

def pt.get_hit(+h: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, eq: {Nat.is_eq(Tr.Ent.k(h), x) == True{} : Bool}) -> {Tr.get(h <> r, x) == Some{h} : Maybe<&2, Tr.Ent>}:
  %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(h), x), True{}, eq) : {Tr.get.go(h <> r, x, _) == Some{h} : Maybe<&2, Tr.Ent>}
  {==}

def pt.get_head(+h: Tr.Ent, +r: List<&2, Tr.Ent>) -> {Tr.get(h <> r, Tr.Ent.k(h)) == Some{h} : Maybe<&2, Tr.Ent>}:
  pt.get_hit(h, r, Tr.Ent.k(h), Equal.sym(Bool, True{}, Nat.is_eq(Tr.Ent.k(h), Tr.Ent.k(h)), LANat.pt.eq_refl(Tr.Ent.k(h))))

def pt.get_miss(+h: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, ne: {Nat.is_eq(Tr.Ent.k(h), x) == False{} : Bool}) -> {Tr.get(h <> r, x) == Tr.get(r, x) : Maybe<&2, Tr.Ent>}:
  %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(h), x), False{}, ne) : {Tr.get.go(h <> r, x, _) == Tr.get(r, x) : Maybe<&2, Tr.Ent>}
  {==}

def pt.get_go_cong(b: Bool, +h: Tr.Ent, +s: List<&2, Tr.Ent>, +r: List<&2, Tr.Ent>, +x: Nat, e: {Tr.get(s, x) == Tr.get(r, x) : Maybe<&2, Tr.Ent>}) -> {Tr.get.go(h <> s, x, b) == Tr.get.go(h <> r, x, b) : Maybe<&2, Tr.Ent>}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

# a lookup sees past a head that agrees
def pt.get_cons_cong(+h: Tr.Ent, +s: List<&2, Tr.Ent>, +r: List<&2, Tr.Ent>, +x: Nat, e: {Tr.get(s, x) == Tr.get(r, x) : Maybe<&2, Tr.Ent>}) -> {Tr.get(h <> s, x) == Tr.get(h <> r, x) : Maybe<&2, Tr.Ent>}:
  pt.get_go_cong(Nat.is_eq(Tr.Ent.k(h), x), h, s, r, x, e)

def pt.get_set_go_same(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, ec: {Tr.first(Tr.Ent.k(e), t) == c : Cmp}) -> {Tr.get(Tr.set.go(t, e, c), Tr.Ent.k(e)) == Some{e} : Maybe<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      pt.get_head(e, Nil{})
    case +h <> +r:
      match c:
        case LT{}:
          pt.get_head(e, h <> r)
        case EQ{}:
          pt.get_head(e, r)
        case GT{}:
          +s = Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r))
          +ne = LNat.pt.lt_ne(Tr.Ent.k(h), Tr.Ent.k(e), LANat.pt.cmp_gt(Tr.Ent.k(e), Tr.Ent.k(h), ec))
          Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h <> s, Tr.Ent.k(e)), Tr.get(s, Tr.Ent.k(e)), Some{e}, pt.get_miss(h, s, Tr.Ent.k(e), ne), pt.get_set_go_same(r, e, Tr.first(Tr.Ent.k(e), r), {==}))

def pt.get_set_same(+t: List<&2, Tr.Ent>, +e: Tr.Ent) -> {Tr.get(Tr.set(t, e), Tr.Ent.k(e)) == Some{e} : Maybe<&2, Tr.Ent>}:
  pt.get_set_go_same(t, e, Tr.first(Tr.Ent.k(e), t), {==})

def pt.get_set_go_other(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, ec: {Tr.first(Tr.Ent.k(e), t) == c : Cmp}, +x: Nat, +ne: {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}) -> {Tr.get(Tr.set.go(t, e, c), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      pt.get_miss(e, Nil{}, x, ne)
    case +h <> +r:
      match c:
        case LT{}:
          pt.get_miss(e, h <> r, x, ne)
        case EQ{}:
          +keq = LALogic.pt.cmp_eq(Tr.Ent.k(e), Tr.Ent.k(h), ec)
          %keq : {Tr.get(e <> r, x) == Tr.get.go(h <> r, x, Nat.is_eq(_, x)) : Maybe<&2, Tr.Ent>}
          %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ne) : {Tr.get.go(e <> r, x, _) == Tr.get.go(h <> r, x, _) : Maybe<&2, Tr.Ent>}
          {==}
        case GT{}:
          pt.get_cons_cong(h, Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), r, x, pt.get_set_go_other(r, e, Tr.first(Tr.Ent.k(e), r), {==}, x, ne))

def pt.get_set_other(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +x: Nat, ne: {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}) -> {Tr.get(Tr.set(t, e), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}:
  pt.get_set_go_other(t, e, Tr.first(Tr.Ent.k(e), t), {==}, x, ne)

def pt.get_unset_go_same(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, eh: {Tr.key.at(t, x) == hit : Bool}) -> {Tr.get(Tr.unset.go(t, x, hit), x) == None{} : Maybe<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.get_unset_go_same(r, x, Tr.key.at(r, x), {==})
        case False{}:
          +u = Tr.unset.go(r, x, Tr.key.at(r, x))
          Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h <> u, x), Tr.get(u, x), None{}, pt.get_miss(h, u, x, eh), pt.get_unset_go_same(r, x, Tr.key.at(r, x), {==}))

def pt.get_unset_same(+t: List<&2, Tr.Ent>, +x: Nat) -> {Tr.get(Tr.unset(t, x), x) == None{} : Maybe<&2, Tr.Ent>}:
  pt.get_unset_go_same(t, x, Tr.key.at(t, x), {==})

def pt.get_unset_go_other(t: List<&2, Tr.Ent>, +y: Nat, hit: Bool, eh: {Tr.key.at(t, y) == hit : Bool}, +x: Nat, +ne: {Nat.is_eq(y, x) == False{} : Bool}) -> {Tr.get(Tr.unset.go(t, y, hit), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +neh = LANat.pt.ne_at(Tr.Ent.k(h), y, x, LALogic.pt.eq_true(Tr.Ent.k(h), y, eh), ne)
          +u = Tr.unset.go(r, y, Tr.key.at(r, y))
          Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(u, x), Tr.get(r, x), Tr.get(h <> r, x), pt.get_unset_go_other(r, y, Tr.key.at(r, y), {==}, x, ne), Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h <> r, x), Tr.get(r, x), pt.get_miss(h, r, x, neh)))
        case False{}:
          pt.get_cons_cong(h, Tr.unset.go(r, y, Tr.key.at(r, y)), r, x, pt.get_unset_go_other(r, y, Tr.key.at(r, y), {==}, x, ne))

def pt.get_unset_other(+t: List<&2, Tr.Ent>, +y: Nat, +x: Nat, ne: {Nat.is_eq(y, x) == False{} : Bool}) -> {Tr.get(Tr.unset(t, y), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}:
  pt.get_unset_go_other(t, y, Tr.key.at(t, y), {==}, x, ne)

def pt.get_below(X: List<&2, Tr.Ent>, +y: Nat, +al: {Tr.above(y, X) == True{} : Bool}, +st: {Tr.sorted(X) == True{} : Bool}) -> {Tr.get(X, y) == None{} : Maybe<&2, Tr.Ent>}:
  match X:
    case Nil{}:
      {==}
    case +h <> +r:
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h <> r, y), Tr.get(r, y), None{}, pt.get_miss(h, r, y, LNat.pt.lt_ne_r(y, Tr.Ent.k(h), al)), pt.get_below(r, y, LATreeAbove.pt.above_tail(y, h, r, al, st), LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)))

def pt.get_put_go(+t: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +v: Nat, +x: Nat, c: Bool, ec: {Nat.is_eq(k, x) == c : Bool}) -> {Tr.get(Tr.set(t, Tr.Ent{k, p, v}), x) == LALogic.tree.pt.pick(c, Some{Tr.Ent{k, p, v}}, Tr.get(t, x)) : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      %LALogic.pt.eq_true(k, x, ec) : {Tr.get(Tr.set(t, Tr.Ent{k, p, v}), _) == Some{Tr.Ent{k, p, v}} : Maybe<&2, Tr.Ent>}
      pt.get_set_same(t, Tr.Ent{k, p, v})
    case False{}:
      pt.get_set_other(t, Tr.Ent{k, p, v}, x, ec)

def pt.get_del_go(+t: List<&2, Tr.Ent>, +y: Nat, +x: Nat, c: Bool, ec: {Nat.is_eq(y, x) == c : Bool}) -> {Tr.get(Tr.unset(t, y), x) == LALogic.tree.pt.pick(c, None{}, Tr.get(t, x)) : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      %LALogic.pt.eq_true(y, x, ec) : {Tr.get(Tr.unset(t, y), _) == None{} : Maybe<&2, Tr.Ent>}
      pt.get_unset_same(t, y)
    case False{}:
      pt.get_unset_other(t, y, x, ec)

def pt.get_exact(+t: List<&2, Tr.Ent>, o: Tr.Op, +x: Nat) -> {Tr.get(Tr.exact(t, o), x) == LALogic.pt.upd(o, Tr.get(t, x), x) : Maybe<&2, Tr.Ent>}:
  match o:
    case Tr.Put{+k, +p, +v}:
      pt.get_put_go(t, k, p, v, x, Nat.is_eq(k, x), {==})
    case Tr.Del{+y}:
      pt.get_del_go(t, y, x, Nat.is_eq(y, x), {==})

def pt.get_patch(ops: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>, +x: Nat) -> {Tr.get(Tr.patch(ops, t), x) == LALogic.pt.look(ops, Tr.get(t, x), x) : Maybe<&2, Tr.Ent>}:
  match ops:
    case Nil{}:
      {==}
    case +o <> +rest:
      +t2 = Tr.exact(t, o)
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(Tr.patch(rest, t2), x), LALogic.pt.look(rest, Tr.get(t2, x), x), LALogic.pt.look(rest, LALogic.pt.upd(o, Tr.get(t, x), x), x), pt.get_patch(rest, t2, x), Equal.cong(Maybe<&2, Tr.Ent>, Maybe<&2, Tr.Ent>, m => LALogic.pt.look(rest, m, x), Tr.get(t2, x), LALogic.pt.upd(o, Tr.get(t, x), x), pt.get_exact(t, o, x)))

def pt.dd_go(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +x: Nat, c: Bool, ec: {Nat.is_eq(Tr.Ent.k(e), x) == c : Bool}, ih: {LALogic.pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), Tr.get(r, x), x) == None{} : Maybe<&2, Tr.Ent>}) -> {LALogic.pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), LALogic.tree.pt.pick(c, None{}, Tr.get(e <> r, x)), x) == None{} : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      LATreeDels.pt.dels_none(r, b, Tr.held.at(r, b), x)
    case False{}:
      %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), pt.get_miss(e, r, x, ec)) : {LALogic.pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), _, x) == None{} : Maybe<&2, Tr.Ent>}
      ih

# the dels drop a key the target lacks
def pt.dels_drop(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.held.at(s, b) == hit : Bool}, +x: Nat, +hb: {Tr.has(b, x) == False{} : Bool}) -> {LALogic.pt.look(Tr.dels.go(s, b, hit), Tr.get(s, x), x) == None{} : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ne = LANat.pt.ne_by2(Tr.Ent.k(e), x, z => Tr.has(b, z), eh, hb)
          %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), pt.get_miss(e, r, x, ne)) : {LALogic.pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), _, x) == None{} : Maybe<&2, Tr.Ent>}
          pt.dels_drop(r, b, Tr.held.at(r, b), {==}, x, hb)
        case False{}:
          pt.dd_go(e, r, b, x, Nat.is_eq(Tr.Ent.k(e), x), {==}, pt.dels_drop(r, b, Tr.held.at(r, b), {==}, x, hb))

def pt.gnh_go(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, c: Bool, ec: {Nat.is_eq(Tr.Ent.k(e), x) == c : Bool}, gn: {Tr.get(e <> r, x) == None{} : Maybe<&2, Tr.Ent>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      LALogic.pt.some_none({True{} == False{} : Bool}, e, Equal.trans(Maybe<&2, Tr.Ent>, Some{e}, Tr.get(e <> r, x), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Some{e}, pt.get_hit(e, r, x, ec)), gn))
    case False{}:
      {==}

def pt.get_none_head(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, gn: {Tr.get(e <> r, x) == None{} : Maybe<&2, Tr.Ent>}) -> {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}:
  pt.gnh_go(e, r, x, Nat.is_eq(Tr.Ent.k(e), x), {==}, gn)

def pt.reach_tail(+a: List<&2, Tr.Ent>, +x: Nat, +z: Tr.Ent, c: Bool, ec: {Tr.same(Tr.get(a, x), Some{z}) == c : Bool}) -> {LALogic.tree.pt.pick(c, Tr.get(a, x), Some{z}) == Some{z} : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      LALogic.pt.same_some(Tr.get(a, x), z, ec)
    case False{}:
      {==}

# below two heads with one key, the lists agree as they did
def pt.agree_strip(es: List<&2, Tr.Ent>, +h1: Tr.Ent, +r1: List<&2, Tr.Ent>, +h2: Tr.Ent, +r2: List<&2, Tr.Ent>, ag: LALogic.pt.Agree(es, h1 <> r1, h2 <> r2), +al: {Tr.above(Tr.Ent.k(h1), es) == True{} : Bool}, +st: {Tr.sorted(es) == True{} : Bool}, +keq: {Tr.Ent.k(h1) == Tr.Ent.k(h2) : Nat}) -> LALogic.pt.Agree(es, r1, r2):
  match es:
    case Nil{}:
      Unit{}
    case +e <> +rest:
      (eq0, agt) = ag
      +k = Tr.Ent.k(e)
      +ne1 = LNat.pt.lt_ne(Tr.Ent.k(h1), k, al)
      +ne2 = LANat.pt.ne_at(Tr.Ent.k(h2), Tr.Ent.k(h1), k, Equal.sym(Nat, Tr.Ent.k(h1), Tr.Ent.k(h2), keq), ne1)
      +hd = Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r1, k), Tr.get(h1 <> r1, k), Tr.get(r2, k), Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, k), Tr.get(r1, k), pt.get_miss(h1, r1, k, ne1)), Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, k), Tr.get(h2 <> r2, k), Tr.get(r2, k), eq0, pt.get_miss(h2, r2, k, ne2)))
      (hd, pt.agree_strip(rest, h1, r1, h2, r2, agt, LATreeAbove.pt.above_tail(Tr.Ent.k(h1), e, rest, al, st), LLogicBool.tree.pt.and_r(Tr.above(k, rest), Tr.sorted(rest), st), keq))

# two sorted lists that agree have the same first key
def pt.ext_head(+h1: Tr.Ent, +r1: List<&2, Tr.Ent>, +h2: Tr.Ent, +r2: List<&2, Tr.Ent>, c: Cmp, ec: {Nat.cmp(Tr.Ent.k(h1), Tr.Ent.k(h2)) == c : Cmp}, e1: {Tr.get(h1 <> r1, Tr.Ent.k(h1)) == Tr.get(h2 <> r2, Tr.Ent.k(h1)) : Maybe<&2, Tr.Ent>}, e2: {Tr.get(h1 <> r1, Tr.Ent.k(h2)) == Tr.get(h2 <> r2, Tr.Ent.k(h2)) : Maybe<&2, Tr.Ent>}, +s1: {Tr.sorted(h1 <> r1) == True{} : Bool}, +s2: {Tr.sorted(h2 <> r2) == True{} : Bool}) -> {Tr.Ent.k(h1) == Tr.Ent.k(h2) : Nat}:
  match c:
    case LT{}:
      +gn = pt.get_below(h2 <> r2, Tr.Ent.k(h1), LANat.pt.cmp_lt(Tr.Ent.k(h1), Tr.Ent.k(h2), ec), s2)
      LALogic.pt.some_none({Tr.Ent.k(h1) == Tr.Ent.k(h2) : Nat}, h1, Equal.trans(Maybe<&2, Tr.Ent>, Some{h1}, Tr.get(h1 <> r1, Tr.Ent.k(h1)), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h1}, pt.get_head(h1, r1)), Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Tr.get(h2 <> r2, Tr.Ent.k(h1)), None{}, e1, gn)))
    case EQ{}:
      LALogic.pt.cmp_eq(Tr.Ent.k(h1), Tr.Ent.k(h2), ec)
    case GT{}:
      +gn = pt.get_below(h1 <> r1, Tr.Ent.k(h2), LANat.pt.cmp_gt(Tr.Ent.k(h1), Tr.Ent.k(h2), ec), s1)
      LALogic.tree.pt.none_some({Tr.Ent.k(h1) == Tr.Ent.k(h2) : Nat}, h2, Equal.trans(Maybe<&2, Tr.Ent>, None{}, Tr.get(h1 <> r1, Tr.Ent.k(h2)), Some{h2}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h2)), None{}, gn), Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h2)), Tr.get(h2 <> r2, Tr.Ent.k(h2)), Some{h2}, e2, pt.get_head(h2, r2))))

def tc.get_app_r(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +la: {LLogicBool.tc.lt(A, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {Tr.get(List.append(&2, Tr.Ent, A, B), x) == Tr.get(B, x) : Maybe<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +e <> +r:
      +R = List.append(&2, Tr.Ent, r, B)
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(e <> R, x), Tr.get(R, x), Tr.get(B, x), pt.get_miss(e, R, x, LNat.tc.lt_miss(e, b, x, LNat.tc.lt_head(e, r, b, la), xb)), tc.get_app_r(r, B, b, x, LLogicBool.tc.lt_tail(e, r, b, la), xb))

def tc.get_none_ge(B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {LLogicBool.tc.ge(B, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Tr.get(B, x) == None{} : Maybe<&2, Tr.Ent>}:
  match B:
    case Nil{}:
      {==}
    case +f <> +r:
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(f <> r, x), Tr.get(r, x), None{}, pt.get_miss(f, r, x, LNat.tc.ge_miss(f, b, x, LNat.tc.ge_head(f, r, b, gb), xb)), tc.get_none_ge(r, b, x, LLogicBool.tc.ge_tail(f, r, b, gb), xb))

def tc.get_app_l(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {LLogicBool.tc.ge(B, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Tr.get(List.append(&2, Tr.Ent, A, B), x) == Tr.get(A, x) : Maybe<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      tc.get_none_ge(B, b, x, gb, xb)
    case +e <> +r:
      pt.get_cons_cong(e, List.append(&2, Tr.Ent, r, B), r, x, tc.get_app_l(r, B, b, x, gb, xb))

def tc.get_go(m: Tr.KMap, +x: Nat, b: Bool, +eb: {Tr.KMap.at(m, x) == b : Bool}, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.get.go(m, x, b) == Tr.get(Tr.KMap.read(m), x) : Maybe<&2, Tr.Ent>}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+e} True{}:
      Equal.sym(Maybe<&2, Tr.Ent>, Tr.get([e], x), Some{e}, pt.get_hit(e, Nil{}, x, eb))
    case Tr.KOne{+e} False{}:
      Equal.sym(Maybe<&2, Tr.Ent>, Tr.get([e], x), None{}, pt.get_miss(e, Nil{}, x, eb))
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +ih = tc.get_go(l, x, Tr.KMap.at(l, x), {==}, LLogicBool.tc.bst_l(mid, mp, l, r, bt))
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.KMap.get(l, x), Tr.get(Tr.KMap.read(l), x), Tr.get(List.append(&2, Tr.Ent, Tr.KMap.read(l), Tr.KMap.read(r)), x), ih, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(List.append(&2, Tr.Ent, Tr.KMap.read(l), Tr.KMap.read(r)), x), Tr.get(Tr.KMap.read(l), x), tc.get_app_l(Tr.KMap.read(l), Tr.KMap.read(r), mid, x, LTree.tc.bst_ge(mid, mp, l, r, bt), eb)))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +ih = tc.get_go(r, x, Tr.KMap.at(r, x), {==}, LBool.tc.bst_r(mid, mp, l, r, bt))
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.KMap.get(r, x), Tr.get(Tr.KMap.read(r), x), Tr.get(List.append(&2, Tr.Ent, Tr.KMap.read(l), Tr.KMap.read(r)), x), ih, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(List.append(&2, Tr.Ent, Tr.KMap.read(l), Tr.KMap.read(r)), x), Tr.get(Tr.KMap.read(r), x), tc.get_app_r(Tr.KMap.read(l), Tr.KMap.read(r), mid, x, LTree.tc.bst_lt(mid, mp, l, r, bt), eb)))

# a lookup down the map is the lookup in its nodes
def tc.get(+m: Tr.KMap, +x: Nat, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.get(m, x) == Tr.get(Tr.KMap.read(m), x) : Maybe<&2, Tr.Ent>}:
  tc.get_go(m, x, Tr.KMap.at(m, x), {==}, bt)

def tc.has(+m: Tr.KMap, +x: Nat, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.has(m, x) == Tr.has(Tr.KMap.read(m), x) : Bool}:
  Equal.cong(Maybe<&2, Tr.Ent>, Bool, y => Maybe.is_some(&2, Tr.Ent, y), Tr.KMap.get(m, x), Tr.get(Tr.KMap.read(m), x), tc.get(m, x, bt))

def tc.hangs(s: List<&2, Tr.Ent>, +m: Tr.KMap, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.hangs(s, m) == Tr.rooted.go(s, Tr.KMap.read(m)) : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +p = Tr.Ent.p(e)
      %Equal.sym(Bool, Tr.KMap.has(m, p), Tr.has(Tr.KMap.read(m), p), tc.has(m, p, bt)) : {Bool.and(Bool.and(Nat.is_lt(p, Tr.Ent.k(e)), Bool.or(Nat.is_eq(p, 0n), _)), Tr.KMap.hangs(rest, m)) == Tr.rooted.go(e <> rest, Tr.KMap.read(m)) : Bool}
      %Equal.sym(Bool, Tr.KMap.hangs(rest, m), Tr.rooted.go(rest, Tr.KMap.read(m)), tc.hangs(rest, m, bt)) : {Bool.and(Bool.and(Nat.is_lt(p, Tr.Ent.k(e)), Bool.or(Nat.is_eq(p, 0n), Tr.has(Tr.KMap.read(m), p))), _) == Tr.rooted.go(e <> rest, Tr.KMap.read(m)) : Bool}
      {==}

# the test of a put on the map is ok on the list
def tc.good_put(+m: Tr.KMap, +k: Nat, +p: Nat, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.KMap.has(m, p))) == Tr.ok(Tr.KMap.read(m), k, p) : Bool}:
  %Equal.sym(Bool, Tr.KMap.has(m, p), Tr.has(Tr.KMap.read(m), p), tc.has(m, p, bt)) : {Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), _)) == Tr.ok(Tr.KMap.read(m), k, p) : Bool}
  {==}

# two sorted lists that agree on their keys are equal
def pt.ext(l1: List<&2, Tr.Ent>, l2: List<&2, Tr.Ent>, +s1: {Tr.sorted(l1) == True{} : Bool}, +s2: {Tr.sorted(l2) == True{} : Bool}, A1: LALogic.pt.Agree(l1, l1, l2), A2: LALogic.pt.Agree(l2, l1, l2)) -> {l1 == l2 : List<&2, Tr.Ent>}:
  match l1 l2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+h2, +r2}:
      (e2, t2) = A2
      LALogic.tree.pt.none_some({Nil{} == h2 <> r2 : List<&2, Tr.Ent>}, h2, Equal.trans(Maybe<&2, Tr.Ent>, None{}, Tr.get(h2 <> r2, Tr.Ent.k(h2)), Some{h2}, e2, pt.get_head(h2, r2)))
    case Con{+h1, +r1} Nil{}:
      (e1, t1) = A1
      LALogic.pt.some_none({h1 <> r1 == Nil{} : List<&2, Tr.Ent>}, h1, Equal.trans(Maybe<&2, Tr.Ent>, Some{h1}, Tr.get(h1 <> r1, Tr.Ent.k(h1)), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h1}, pt.get_head(h1, r1)), e1))
    case Con{+h1, +r1} Con{+h2, +r2}:
      (+e1, t1) = A1
      (+e2, t2) = A2
      +keq = pt.ext_head(h1, r1, h2, r2, Nat.cmp(Tr.Ent.k(h1), Tr.Ent.k(h2)), {==}, e1, e2, s1, s2)
      +s1t = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h1), r1), Tr.sorted(r1), s1)
      +s2t = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h2), r2), Tr.sorted(r2), s2)
      +al1 = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(h1), r1), Tr.sorted(r1), s1)
      +al2 = Equal.trans(Bool, Tr.above(Tr.Ent.k(h1), r2), Tr.above(Tr.Ent.k(h2), r2), True{}, Equal.cong(Nat, Bool, n => Tr.above(n, r2), Tr.Ent.k(h1), Tr.Ent.k(h2), keq), LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(h2), r2), Tr.sorted(r2), s2))
      +ih = pt.ext(r1, r2, s1t, s2t, pt.agree_strip(r1, h1, r1, h2, r2, t1, al1, s1t, keq), pt.agree_strip(r2, h1, r1, h2, r2, t2, al2, s2t, keq))
      +hs = Equal.trans(Maybe<&2, Tr.Ent>, Some{h1}, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h2}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h1}, pt.get_head(h1, r1)), Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Tr.get(h2 <> r2, Tr.Ent.k(h1)), Some{h2}, e1, pt.get_hit(h2, r2, Tr.Ent.k(h1), LANat.pt.eq_of(Tr.Ent.k(h1), Tr.Ent.k(h2), keq))))
      %LALogic.tree.pt.some_inj(h1, h2, hs) : {h1 <> r1 == _ <> r2 : List<&2, Tr.Ent>}
      %ih : {h1 <> r1 == h1 <> _ : List<&2, Tr.Ent>}
      {==}
