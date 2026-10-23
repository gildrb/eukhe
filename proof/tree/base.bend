# eukhe: lemmas the proofs of area tree share

import Base
import ../../bend/tree.bend as Tr
import ../../bend/director.bend as Dr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_tree.bend as Ft
import ../../LAWS.bend as Laws
import ../base.bend as L

def pt.MD(m: Maybe<&2, Tr.Ent>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

def tree.pt.none_some(-A: Type, -x: Tr.Ent, e: {None{} == Some{x} : Maybe<&2, Tr.Ent>}) -> A:
  %e : pt.MD(_, Unit, A)
  Unit{}

def pt.some_none(-A: Type, -x: Tr.Ent, e: {Some{x} == None{} : Maybe<&2, Tr.Ent>}) -> A:
  %e : pt.MD(_, A, Unit)
  Unit{}

def pt.CD(c: Cmp, l: Type, e: Type, g: Type) -> Type:
  match c:
    case LT{}:
      l
    case EQ{}:
      e
    case GT{}:
      g

def pt.or_l(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      L.pt.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pt.or_r(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      L.pt.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def pt.or_tl(+a: Bool, +b: Bool, ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.or(_, b) == True{} : Bool}
  {==}

def pt.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def pt.flip(-a: Bool, h: {a == True{} : Bool}, g: {a == False{} : Bool}) -> Empty:
  L.pt.absurd(Empty, Equal.trans(Bool, True{}, a, False{}, Equal.sym(Bool, a, True{}, h), g))

# Numbers
# -------

def pt.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pt.eq_refl(p)

def pt.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      L.tree.pt.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      L.tree.pt.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pt.eq_true(p, q, h))

def pt.lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      L.tree.pt.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      L.tree.pt.absurdF({Nat.is_lt(a, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      pt.lt_trans(p, q, r, ab, bc)

def pt.cmp_eq(a: Nat, b: Nat, h: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %h : pt.CD(_, Unit, {0n == 1n+q : Nat}, Unit)
      Unit{}
    case 1n+p 0n:
      %h : pt.CD(_, Unit, {1n+p == 0n : Nat}, Unit)
      Unit{}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pt.cmp_eq(p, q, h))

def pt.cmp_gt(a: Nat, b: Nat, h: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      %h : pt.CD(_, Unit, Unit, {Nat.is_lt(0n, 0n) == True{} : Bool})
      Unit{}
    case 0n 1n+q:
      %h : pt.CD(_, Unit, Unit, {Nat.is_lt(1n+q, 0n) == True{} : Bool})
      Unit{}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pt.cmp_gt(p, q, h)

def pt.cmp_lt(+a: Nat, +b: Nat, h: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, b), LT{}, h) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

# Nodes
# -----

def pt.ent_eta(e: Tr.Ent) -> {Tr.Ent{Tr.Ent.k(e), Tr.Ent.p(e), Tr.Ent.v(e)} == e : Tr.Ent}:
  match e:
    case Tr.Ent{k, p, v}:
      {==}

def pt.ent_refl(e: Tr.Ent) -> {Tr.Ent.eq(e, e) == True{} : Bool}:
  match e:
    case Tr.Ent{+k, +p, +v}:
      %pt.eq_refl(k) : {Bool.and(_, Bool.and(Nat.is_eq(p, p), Nat.is_eq(v, v))) == True{} : Bool}
      %pt.eq_refl(p) : {Bool.and(True{}, Bool.and(_, Nat.is_eq(v, v))) == True{} : Bool}
      %pt.eq_refl(v) : {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
      {==}

def pt.ent_true(a: Tr.Ent, b: Tr.Ent, +h: {Tr.Ent.eq(a, b) == True{} : Bool}) -> {a == b : Tr.Ent}:
  match a b:
    case Tr.Ent{+ak, +ap, +av} Tr.Ent{+bk, +bp, +bv}:
      +hk = pt.eq_true(ak, bk, L.tree.pt.and_l(Nat.is_eq(ak, bk), Bool.and(Nat.is_eq(ap, bp), Nat.is_eq(av, bv)), h))
      +h2 = L.tree.pt.and_r(Nat.is_eq(ak, bk), Bool.and(Nat.is_eq(ap, bp), Nat.is_eq(av, bv)), h)
      +hp = pt.eq_true(ap, bp, L.tree.pt.and_l(Nat.is_eq(ap, bp), Nat.is_eq(av, bv), h2))
      +hv = pt.eq_true(av, bv, L.tree.pt.and_r(Nat.is_eq(ap, bp), Nat.is_eq(av, bv), h2))
      %hk : {Tr.Ent{ak, ap, av} == Tr.Ent{_, bp, bv} : Tr.Ent}
      %hp : {Tr.Ent{ak, ap, av} == Tr.Ent{ak, _, bv} : Tr.Ent}
      %hv : {Tr.Ent{ak, ap, av} == Tr.Ent{ak, ap, _} : Tr.Ent}
      {==}

# a lookup that is the same as Some{e} is Some{e}
def pt.same_some(m: Maybe<&2, Tr.Ent>, +e: Tr.Ent, h: {Tr.same(m, Some{e}) == True{} : Bool}) -> {m == Some{e} : Maybe<&2, Tr.Ent>}:
  match m:
    case None{}:
      L.tree.pt.absurdF({None{} == Some{e} : Maybe<&2, Tr.Ent>}, h)
    case Some{x}:
      Equal.cong(Tr.Ent, Maybe<&2, Tr.Ent>, y => Some{y}, x, e, pt.ent_true(x, e, h))

def pt.same_refl(+e: Tr.Ent) -> {Tr.same(Some{e}, Some{e}) == True{} : Bool}:
  pt.ent_refl(e)

# Lookup
# ------

def pt.get_hit(+h: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, eq: {Nat.is_eq(Tr.Ent.k(h), x) == True{} : Bool}) -> {Tr.get(h <> r, x) == Some{h} : Maybe<&2, Tr.Ent>}:
  %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(h), x), True{}, eq) : {Tr.get.go(h <> r, x, _) == Some{h} : Maybe<&2, Tr.Ent>}
  {==}

def pt.get_head(+h: Tr.Ent, +r: List<&2, Tr.Ent>) -> {Tr.get(h <> r, Tr.Ent.k(h)) == Some{h} : Maybe<&2, Tr.Ent>}:
  pt.get_hit(h, r, Tr.Ent.k(h), Equal.sym(Bool, True{}, Nat.is_eq(Tr.Ent.k(h), Tr.Ent.k(h)), pt.eq_refl(Tr.Ent.k(h))))

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
          +ne = L.pt.lt_ne(Tr.Ent.k(h), Tr.Ent.k(e), pt.cmp_gt(Tr.Ent.k(e), Tr.Ent.k(h), ec))
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
          +keq = pt.cmp_eq(Tr.Ent.k(e), Tr.Ent.k(h), ec)
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

def pt.ne_at(+a: Nat, +y: Nat, +x: Nat, ay: {a == y : Nat}, ne: {Nat.is_eq(y, x) == False{} : Bool}) -> {Nat.is_eq(a, x) == False{} : Bool}:
  %Equal.sym(Nat, a, y, ay) : {Nat.is_eq(_, x) == False{} : Bool}
  ne

def pt.get_unset_go_other(t: List<&2, Tr.Ent>, +y: Nat, hit: Bool, eh: {Tr.key.at(t, y) == hit : Bool}, +x: Nat, +ne: {Nat.is_eq(y, x) == False{} : Bool}) -> {Tr.get(Tr.unset.go(t, y, hit), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +neh = pt.ne_at(Tr.Ent.k(h), y, x, pt.eq_true(Tr.Ent.k(h), y, eh), ne)
          +u = Tr.unset.go(r, y, Tr.key.at(r, y))
          Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(u, x), Tr.get(r, x), Tr.get(h <> r, x), pt.get_unset_go_other(r, y, Tr.key.at(r, y), {==}, x, ne), Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h <> r, x), Tr.get(r, x), pt.get_miss(h, r, x, neh)))
        case False{}:
          pt.get_cons_cong(h, Tr.unset.go(r, y, Tr.key.at(r, y)), r, x, pt.get_unset_go_other(r, y, Tr.key.at(r, y), {==}, x, ne))

def pt.get_unset_other(+t: List<&2, Tr.Ent>, +y: Nat, +x: Nat, ne: {Nat.is_eq(y, x) == False{} : Bool}) -> {Tr.get(Tr.unset(t, y), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}:
  pt.get_unset_go_other(t, y, Tr.key.at(t, y), {==}, x, ne)

# Order
# -----

def pt.above_set_go(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, +l: Nat, al: {Tr.above(l, t) == True{} : Bool}, le: {Nat.is_lt(l, Tr.Ent.k(e)) == True{} : Bool}) -> {Tr.above(l, Tr.set.go(t, e, c)) == True{} : Bool}:
  match t:
    case Nil{}:
      le
    case +h <> +r:
      match c:
        case LT{}:
          le
        case EQ{}:
          le
        case GT{}:
          al

def pt.sorted_set_go(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, ec: {Tr.first(Tr.Ent.k(e), t) == c : Cmp}, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.set.go(t, e, c)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match c:
        case LT{}:
          L.tree.pt.and_t(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(h)), Tr.sorted(h <> r), pt.cmp_lt(Tr.Ent.k(e), Tr.Ent.k(h), ec), st)
        case EQ{}:
          %Equal.sym(Nat, Tr.Ent.k(e), Tr.Ent.k(h), pt.cmp_eq(Tr.Ent.k(e), Tr.Ent.k(h), ec)) : {Bool.and(Tr.above(_, r), Tr.sorted(r)) == True{} : Bool}
          st
        case GT{}:
          +s = Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r))
          +al = L.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          L.tree.pt.and_t(Tr.above(Tr.Ent.k(h), s), Tr.sorted(s), pt.above_set_go(r, e, Tr.first(Tr.Ent.k(e), r), Tr.Ent.k(h), al, pt.cmp_gt(Tr.Ent.k(e), Tr.Ent.k(h), ec)), pt.sorted_set_go(r, e, Tr.first(Tr.Ent.k(e), r), {==}, sr))

def pt.above_tail(+l: Nat, +h: Tr.Ent, r: List<&2, Tr.Ent>, al: {Tr.above(l, h <> r) == True{} : Bool}, st: {Tr.sorted(h <> r) == True{} : Bool}) -> {Tr.above(l, r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +h2 <> +r2:
      pt.lt_trans(l, Tr.Ent.k(h), Tr.Ent.k(h2), al, L.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(h), Tr.Ent.k(h2)), Tr.sorted(h2 <> r2), st))

def pt.above_unset_go(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +l: Nat, al: {Tr.above(l, t) == True{} : Bool}, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.above(l, Tr.unset.go(t, x, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.above_unset_go(r, x, Tr.key.at(r, x), l, pt.above_tail(l, h, r, al, st), L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          al

def pt.sorted_unset_go(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.unset.go(t, x, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.sorted_unset_go(r, x, Tr.key.at(r, x), L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          +u = Tr.unset.go(r, x, Tr.key.at(r, x))
          L.tree.pt.and_t(Tr.above(Tr.Ent.k(h), u), Tr.sorted(u), pt.above_unset_go(r, x, Tr.key.at(r, x), Tr.Ent.k(h), L.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st), sr), pt.sorted_unset_go(r, x, Tr.key.at(r, x), sr))

def pt.sorted_exact(+t: List<&2, Tr.Ent>, o: Tr.Op, st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.exact(t, o)) == True{} : Bool}:
  match o:
    case Tr.Put{+k, +p, +v}:
      pt.sorted_set_go(t, Tr.Ent{k, p, v}, Tr.first(k, t), {==}, st)
    case Tr.Del{+x}:
      pt.sorted_unset_go(t, x, Tr.key.at(t, x), st)

def pt.sorted_patch(ops: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>, st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.patch(ops, t)) == True{} : Bool}:
  match ops:
    case Nil{}:
      st
    case +o <> rest:
      pt.sorted_patch(rest, Tr.exact(t, o), pt.sorted_exact(t, o, st))

# Membership
# ----------

def pt.void(-A: Type, e: Empty) -> A:
  match e:

def tree.pt.or_false_r(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pt.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# an or whose right side is false holds by its left side
def pt.or_l_true(a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}, nb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pt.void({False{} == True{} : Bool}, pt.flip(b, h, nb))

def pt.has_cons_go(b: Bool, +h: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat) -> {Maybe.is_some(&2, Tr.Ent, Tr.get.go(h <> r, y, b)) == Bool.or(b, Tr.has(r, y)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pt.has_cons(+h: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat) -> {Tr.has(h <> r, y) == Bool.or(Nat.is_eq(Tr.Ent.k(h), y), Tr.has(r, y)) : Bool}:
  pt.has_cons_go(Nat.is_eq(Tr.Ent.k(h), y), h, r, y)

def pt.has_miss(+h: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat, ne: {Nat.is_eq(Tr.Ent.k(h), y) == False{} : Bool}) -> {Tr.has(h <> r, y) == Tr.has(r, y) : Bool}:
  Equal.cong(Maybe<&2, Tr.Ent>, Bool, m => Maybe.is_some(&2, Tr.Ent, m), Tr.get(h <> r, y), Tr.get(r, y), pt.get_miss(h, r, y, ne))

def pt.has_head(+h: Tr.Ent, +r: List<&2, Tr.Ent>) -> {Tr.has(h <> r, Tr.Ent.k(h)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h <> r, Tr.Ent.k(h)), Some{h}, pt.get_head(h, r)) : {Maybe.is_some(&2, Tr.Ent, _) == True{} : Bool}
  {==}

def pt.has_app(A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +y: Nat) -> {Tr.has(List.append(&2, Tr.Ent, A, C), y) == Bool.or(Tr.has(A, y), Tr.has(C, y)) : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +ea = Nat.is_eq(Tr.Ent.k(a), y)
      +rc = List.append(&2, Tr.Ent, r, C)
      %Equal.sym(Bool, Tr.has(a <> rc, y), Bool.or(ea, Tr.has(rc, y)), pt.has_cons(a, rc, y)) : {_ == Bool.or(Tr.has(a <> r, y), Tr.has(C, y)) : Bool}
      %Equal.sym(Bool, Tr.has(rc, y), Bool.or(Tr.has(r, y), Tr.has(C, y)), pt.has_app(r, C, y)) : {Bool.or(ea, _) == Bool.or(Tr.has(a <> r, y), Tr.has(C, y)) : Bool}
      %Equal.sym(Bool, Tr.has(a <> r, y), Bool.or(ea, Tr.has(r, y)), pt.has_cons(a, r, y)) : {Bool.or(ea, Bool.or(Tr.has(r, y), Tr.has(C, y))) == Bool.or(_, Tr.has(C, y)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(ea, Tr.has(r, y)), Tr.has(C, y)), Bool.or(ea, Bool.or(Tr.has(r, y), Tr.has(C, y))), pt.or_assoc(ea, Tr.has(r, y), Tr.has(C, y)))

def pt.has_app_l(+A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +y: Nat, h: {Tr.has(A, y) == True{} : Bool}) -> {Tr.has(List.append(&2, Tr.Ent, A, C), y) == True{} : Bool}:
  %Equal.sym(Bool, Tr.has(List.append(&2, Tr.Ent, A, C), y), Bool.or(Tr.has(A, y), Tr.has(C, y)), pt.has_app(A, C, y)) : {_ == True{} : Bool}
  pt.or_tl(Tr.has(A, y), Tr.has(C, y), h)

def pt.has_app_r(+A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +y: Nat, h: {Tr.has(C, y) == True{} : Bool}) -> {Tr.has(List.append(&2, Tr.Ent, A, C), y) == True{} : Bool}:
  %Equal.sym(Bool, Tr.has(List.append(&2, Tr.Ent, A, C), y), Bool.or(Tr.has(A, y), Tr.has(C, y)), pt.has_app(A, C, y)) : {_ == True{} : Bool}
  pt.or_tr(Tr.has(A, y), Tr.has(C, y), h)

# no node of a sorted list is below its first key
def pt.has_below(X: List<&2, Tr.Ent>, +y: Nat, +al: {Tr.above(y, X) == True{} : Bool}, +st: {Tr.sorted(X) == True{} : Bool}) -> {Tr.has(X, y) == False{} : Bool}:
  match X:
    case Nil{}:
      {==}
    case +h <> +r:
      Equal.trans(Bool, Tr.has(h <> r, y), Tr.has(r, y), False{}, pt.has_miss(h, r, y, L.pt.lt_ne_r(y, Tr.Ent.k(h), al)), pt.has_below(r, y, pt.above_tail(y, h, r, al, st), L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)))

def pt.app_snoc(A: List<&2, Tr.Ent>, +e: Tr.Ent, +C: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, A, [e]), C) == List.append(&2, Tr.Ent, A, e <> C) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, l => a <> l, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, r, [e]), C), List.append(&2, Tr.Ent, r, e <> C), pt.app_snoc(r, e, C))

def pt.sorted_app_r(A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, st: {Tr.sorted(List.append(&2, Tr.Ent, A, C)) == True{} : Bool}) -> {Tr.sorted(C) == True{} : Bool}:
  match A:
    case Nil{}:
      st
    case +a <> +r:
      pt.sorted_app_r(r, C, L.tree.pt.and_r(Tr.above(Tr.Ent.k(a), List.append(&2, Tr.Ent, r, C)), Tr.sorted(List.append(&2, Tr.Ent, r, C)), st))

# A put
# -----

def pt.has_set_go(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +y: Nat, b: Bool, eb: {Nat.is_eq(Tr.Ent.k(e), y) == b : Bool}, h: {Tr.has(t, y) == True{} : Bool}) -> {Tr.has(Tr.set(t, e), y) == True{} : Bool}:
  match b:
    case True{}:
      %pt.eq_true(Tr.Ent.k(e), y, eb) : {Tr.has(Tr.set(t, e), _) == True{} : Bool}
      %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(Tr.set(t, e), Tr.Ent.k(e)), Some{e}, pt.get_set_same(t, e)) : {Maybe.is_some(&2, Tr.Ent, _) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(Tr.set(t, e), y), Tr.get(t, y), pt.get_set_other(t, e, y, eb)) : {Maybe.is_some(&2, Tr.Ent, _) == True{} : Bool}
      h

# a set keeps every node there
def pt.has_set(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +y: Nat, h: {Tr.has(t, y) == True{} : Bool}) -> {Tr.has(Tr.set(t, e), y) == True{} : Bool}:
  pt.has_set_go(t, e, y, Nat.is_eq(Tr.Ent.k(e), y), {==}, h)

def pt.or_has_set(b: Bool, +t: List<&2, Tr.Ent>, +e: Tr.Ent, +p: Nat, o: {Bool.or(b, Tr.has(t, p)) == True{} : Bool}) -> {Bool.or(b, Tr.has(Tr.set(t, e), p)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pt.has_set(t, e, p, o)

def pt.ok_set(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +k: Nat, +p: Nat, +h: {Tr.ok(t, k, p) == True{} : Bool}) -> {Tr.ok(Tr.set(t, e), k, p) == True{} : Bool}:
  +o = L.tree.pt.and_r(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(t, p)), h)
  L.tree.pt.and_t(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(Tr.set(t, e), p)), L.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(t, p)), h), pt.or_has_set(Nat.is_eq(p, 0n), t, e, p, o))

def pt.rooted_mono_set(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +e: Tr.Ent, +rs: {Tr.rooted.go(s, all) == True{} : Bool}) -> {Tr.rooted.go(s, Tr.set(all, e)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +h <> +r:
      +oh = L.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)
      +rr = L.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)
      L.tree.pt.and_t(Tr.ok(Tr.set(all, e), Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, Tr.set(all, e)), pt.ok_set(all, e, Tr.Ent.k(h), Tr.Ent.p(h), oh), pt.rooted_mono_set(r, all, e, rr))

def pt.rooted_set_go(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, +rs: {Tr.rooted.go(s, all) == True{} : Bool}, +oe: {Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)) == True{} : Bool}) -> {Tr.rooted.go(Tr.set.go(s, e, c), Tr.set(all, e)) == True{} : Bool}:
  match s:
    case Nil{}:
      L.tree.pt.and_t(Tr.ok(Tr.set(all, e), Tr.Ent.k(e), Tr.Ent.p(e)), True{}, pt.ok_set(all, e, Tr.Ent.k(e), Tr.Ent.p(e), oe), {==})
    case +h <> +r:
      match c:
        case LT{}:
          L.tree.pt.and_t(Tr.ok(Tr.set(all, e), Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(h <> r, Tr.set(all, e)), pt.ok_set(all, e, Tr.Ent.k(e), Tr.Ent.p(e), oe), pt.rooted_mono_set(h <> r, all, e, rs))
        case EQ{}:
          L.tree.pt.and_t(Tr.ok(Tr.set(all, e), Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, Tr.set(all, e)), pt.ok_set(all, e, Tr.Ent.k(e), Tr.Ent.p(e), oe), pt.rooted_mono_set(r, all, e, L.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)))
        case GT{}:
          +na = Tr.set(all, e)
          +oh = L.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)
          +rr = L.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(r, all), rs)
          L.tree.pt.and_t(Tr.ok(na, Tr.Ent.k(h), Tr.Ent.p(h)), Tr.rooted.go(Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), na), pt.ok_set(all, e, Tr.Ent.k(h), Tr.Ent.p(h), oh), pt.rooted_set_go(r, all, e, Tr.first(Tr.Ent.k(e), r), rr, oe))

def pt.put_sound(+t: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +v: Nat, b: Bool, eb: {Tr.ok(t, k, p) == b : Bool}, +st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.put.at(b, t, Tr.Ent{k, p, v})) == True{} : Bool}:
  match b:
    case True{}:
      +e = {Tr.Ent{k, p, v} : Tr.Ent}
      +s = Tr.set(t, e)
      L.tree.pt.and_t(Tr.sorted(s), Tr.rooted(s), pt.sorted_set_go(t, e, Tr.first(k, t), {==}, L.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), st)), pt.rooted_set_go(t, t, e, Tr.first(k, t), L.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), st), eb))
    case False{}:
      st

# A delete
# --------

def pt.above_prune_go(t: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +l: Nat, al: {Tr.above(l, t) == True{} : Bool}, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.above(l, Tr.prune.go(t, gone, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +g2 = {Tr.Ent.k(h) <> gone : List<&2, Nat>}
          pt.above_prune_go(r, g2, Tr.gone.at(r, g2), l, pt.above_tail(l, h, r, al, st), L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          al

def pt.sorted_prune_go(t: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.prune.go(t, gone, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +g2 = {Tr.Ent.k(h) <> gone : List<&2, Nat>}
          pt.sorted_prune_go(r, g2, Tr.gone.at(r, g2), L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          +u = Tr.prune.go(r, gone, Tr.gone.at(r, gone))
          L.tree.pt.and_t(Tr.above(Tr.Ent.k(h), u), Tr.sorted(u), pt.above_prune_go(r, gone, Tr.gone.at(r, gone), Tr.Ent.k(h), L.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st), sr), pt.sorted_prune_go(r, gone, Tr.gone.at(r, gone), sr))

# every node of pre is kept in b, or its key is gone
def pt.cov(pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +gone: List<&2, Nat>) -> Bool:
  match pre:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Bool.or(Tr.has(b, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.k(e))), pt.cov(rest, b, gone))

# every node of s hangs under the root, a node of pre, or a node before it
def pt.upl(s: List<&2, Tr.Ent>, +pre: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Tr.ok(pre, Tr.Ent.k(e), Tr.Ent.p(e)), pt.upl(rest, List.append(&2, Tr.Ent, pre, [e])))

def pt.cov_app(A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +ca: {pt.cov(A, b, g) == True{} : Bool}, +cc: {pt.cov(C, b, g) == True{} : Bool}) -> {pt.cov(List.append(&2, Tr.Ent, A, C), b, g) == True{} : Bool}:
  match A:
    case Nil{}:
      cc
    case +a <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a)))
      L.tree.pt.and_t(i, pt.cov(List.append(&2, Tr.Ent, r, C), b, g), L.tree.pt.and_l(i, pt.cov(r, b, g), ca), pt.cov_app(r, C, b, g, L.tree.pt.and_r(i, pt.cov(r, b, g), ca), cc))

def pt.or_mono_elem(c: Bool, +g: List<&2, Nat>, +y: Nat, +x: Nat, h: {Bool.or(c, Tr.elem(g, x)) == True{} : Bool}) -> {Bool.or(c, Tr.elem(y <> g, x)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pt.or_tr(Nat.is_eq(y, x), Tr.elem(g, x), h)

def pt.cov_gone(A: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +y: Nat, +ca: {pt.cov(A, b, g) == True{} : Bool}) -> {pt.cov(A, b, y <> g) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a)))
      L.tree.pt.and_t(Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(y <> g, Tr.Ent.k(a))), pt.cov(r, b, y <> g), pt.or_mono_elem(Tr.has(b, Tr.Ent.k(a)), g, y, Tr.Ent.k(a), L.tree.pt.and_l(i, pt.cov(r, b, g), ca)), pt.cov_gone(r, b, g, y, L.tree.pt.and_r(i, pt.cov(r, b, g), ca)))

def pt.or_mono_app(+b: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +g: List<&2, Nat>, +x: Nat, c: Bool, ec: {Tr.has(b, x) == c : Bool}, h: {Bool.or(c, Tr.elem(g, x)) == True{} : Bool}) -> {Bool.or(Tr.has(List.append(&2, Tr.Ent, b, C), x), Tr.elem(g, x)) == True{} : Bool}:
  match c:
    case True{}:
      pt.or_tl(Tr.has(List.append(&2, Tr.Ent, b, C), x), Tr.elem(g, x), pt.has_app_l(b, C, x, ec))
    case False{}:
      pt.or_tr(Tr.has(List.append(&2, Tr.Ent, b, C), x), Tr.elem(g, x), h)

def pt.cov_b(A: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +g: List<&2, Nat>, +ca: {pt.cov(A, b, g) == True{} : Bool}) -> {pt.cov(A, List.append(&2, Tr.Ent, b, C), g) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a)))
      L.tree.pt.and_t(Bool.or(Tr.has(List.append(&2, Tr.Ent, b, C), Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a))), pt.cov(r, List.append(&2, Tr.Ent, b, C), g), pt.or_mono_app(b, C, g, Tr.Ent.k(a), Tr.has(b, Tr.Ent.k(a)), {==}, L.tree.pt.and_l(i, pt.cov(r, b, g), ca)), pt.cov_b(r, b, C, g, L.tree.pt.and_r(i, pt.cov(r, b, g), ca)))

def pt.cov_has_go(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +y: Nat, c: Bool, ec: {Nat.is_eq(Tr.Ent.k(e), y) == c : Bool}, he: {Bool.or(Tr.has(b, Tr.Ent.k(e)), Tr.elem(g, Tr.Ent.k(e))) == True{} : Bool}, ih: {Tr.has(r, y) == True{} : Bool} -> {Bool.or(Tr.has(b, y), Tr.elem(g, y)) == True{} : Bool}, hp: {Tr.has(e <> r, y) == True{} : Bool}) -> {Bool.or(Tr.has(b, y), Tr.elem(g, y)) == True{} : Bool}:
  match c:
    case True{}:
      %pt.eq_true(Tr.Ent.k(e), y, ec) : {Bool.or(Tr.has(b, _), Tr.elem(g, _)) == True{} : Bool}
      he
    case False{}:
      ih(Equal.trans(Bool, Tr.has(r, y), Tr.has(e <> r, y), True{}, Equal.sym(Bool, Tr.has(e <> r, y), Tr.has(r, y), pt.has_miss(e, r, y, ec)), hp))

# a node of pre is kept or gone
def pt.cov_has(pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +y: Nat, +cv: {pt.cov(pre, b, g) == True{} : Bool}) -> {Tr.has(pre, y) == True{} : Bool} -> {Bool.or(Tr.has(b, y), Tr.elem(g, y)) == True{} : Bool}:
  match pre:
    case Nil{}:
      hp => L.tree.pt.absurdF({Bool.or(Tr.has(b, y), Tr.elem(g, y)) == True{} : Bool}, hp)
    case +e <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(e)), Tr.elem(g, Tr.Ent.k(e)))
      +he = L.tree.pt.and_l(i, pt.cov(r, b, g), cv)
      ih = pt.cov_has(r, b, g, y, L.tree.pt.and_r(i, pt.cov(r, b, g), cv))
      hp => pt.cov_has_go(e, r, b, g, y, Nat.is_eq(Tr.Ent.k(e), y), {==}, he, ih, hp)

def pt.ok_keep_go(c: Bool, +pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +gone: List<&2, Nat>, +X: List<&2, Tr.Ent>, +p: Nat, o: {Bool.or(c, Tr.has(pre, p)) == True{} : Bool}, +cv: {pt.cov(pre, b, gone) == True{} : Bool}, ng: {Tr.elem(gone, p) == False{} : Bool}) -> {Bool.or(c, Tr.has(List.append(&2, Tr.Ent, b, X), p)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +q = pt.cov_has(pre, b, gone, p, cv)(o)
      pt.has_app_l(b, X, p, pt.or_l_true(Tr.has(b, p), Tr.elem(gone, p), q, ng))

# a kept node still hangs under the root or a kept node
def pt.ok_keep(+pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +gone: List<&2, Nat>, +X: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +op: {Tr.ok(pre, k, p) == True{} : Bool}, +cv: {pt.cov(pre, b, gone) == True{} : Bool}, ng: {Tr.elem(gone, p) == False{} : Bool}) -> {Tr.ok(List.append(&2, Tr.Ent, b, X), k, p) == True{} : Bool}:
  +o = L.tree.pt.and_r(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(pre, p)), op)
  L.tree.pt.and_t(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(List.append(&2, Tr.Ent, b, X), p)), L.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(pre, p)), op), pt.ok_keep_go(Nat.is_eq(p, 0n), pre, b, gone, X, p, o, cv, ng))

def pt.upl_of(s: List<&2, Tr.Ent>, +pre: List<&2, Tr.Ent>, +rs: {Tr.rooted.go(s, List.append(&2, Tr.Ent, pre, s)) == True{} : Bool}, +st: {Tr.sorted(List.append(&2, Tr.Ent, pre, s)) == True{} : Bool}) -> {pt.upl(s, pre) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +k = Tr.Ent.k(e)
      +p = Tr.Ent.p(e)
      +X = {e <> r : List<&2, Tr.Ent>}
      +A = List.append(&2, Tr.Ent, pre, X)
      +pre2 = List.append(&2, Tr.Ent, pre, [e])
      +oA = L.tree.pt.and_l(Tr.ok(A, k, p), Tr.rooted.go(r, A), rs)
      +lt = L.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(A, p)), oA)
      +hx = pt.has_below(X, p, lt, pt.sorted_app_r(pre, X, st))
      +hp = Equal.trans(Bool, Tr.has(A, p), Bool.or(Tr.has(pre, p), Tr.has(X, p)), Tr.has(pre, p), pt.has_app(pre, X, p), Equal.trans(Bool, Bool.or(Tr.has(pre, p), Tr.has(X, p)), Bool.or(Tr.has(pre, p), False{}), Tr.has(pre, p), Equal.cong(Bool, Bool, z => Bool.or(Tr.has(pre, p), z), Tr.has(X, p), False{}, hx), tree.pt.or_false_r(Tr.has(pre, p))))
      +okp = Equal.trans(Bool, Tr.ok(pre, k, p), Tr.ok(A, k, p), True{}, Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), z)), Tr.has(pre, p), Tr.has(A, p), Equal.sym(Bool, Tr.has(A, p), Tr.has(pre, p), hp)), oA)
      +eq = pt.app_snoc(pre, e, r)
      +rs2 = Equal.trans(Bool, Tr.rooted.go(r, List.append(&2, Tr.Ent, pre2, r)), Tr.rooted.go(r, A), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, l => Tr.rooted.go(r, l), List.append(&2, Tr.Ent, pre2, r), A, eq), L.tree.pt.and_r(Tr.ok(A, k, p), Tr.rooted.go(r, A), rs))
      +st2 = Equal.trans(Bool, Tr.sorted(List.append(&2, Tr.Ent, pre2, r)), Tr.sorted(A), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, l => Tr.sorted(l), List.append(&2, Tr.Ent, pre2, r), A, eq), st)
      L.tree.pt.and_t(Tr.ok(pre, k, p), pt.upl(r, pre2), okp, pt.upl_of(r, pre2, rs2, st2))

# the nodes prune keeps hang under the root or under kept nodes
def pt.rooted_prune_go(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, eh: {Tr.gone.at(s, gone) == hit : Bool}, +pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +cv: {pt.cov(pre, b, gone) == True{} : Bool}, +up: {pt.upl(s, pre) == True{} : Bool}) -> {Tr.rooted.go(Tr.prune.go(s, gone, hit), List.append(&2, Tr.Ent, b, Tr.prune.go(s, gone, hit))) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +k = Tr.Ent.k(e)
          +g2 = {k <> gone : List<&2, Nat>}
          +pre2 = List.append(&2, Tr.Ent, pre, [e])
          +c1 = L.tree.pt.and_t(Bool.or(Tr.has(b, k), Tr.elem(g2, k)), True{}, pt.or_tr(Tr.has(b, k), Tr.elem(g2, k), pt.or_tl(Nat.is_eq(k, k), Tr.elem(gone, k), Equal.sym(Bool, True{}, Nat.is_eq(k, k), pt.eq_refl(k)))), {==})
          +cv2 = pt.cov_app(pre, [e], b, g2, pt.cov_gone(pre, b, gone, k, cv), c1)
          pt.rooted_prune_go(r, g2, Tr.gone.at(r, g2), {==}, pre2, b, cv2, L.tree.pt.and_r(Tr.ok(pre, k, Tr.Ent.p(e)), pt.upl(r, pre2), up))
        case False{}:
          +k = Tr.Ent.k(e)
          +p = Tr.Ent.p(e)
          +P = Tr.prune.go(r, gone, Tr.gone.at(r, gone))
          +pre2 = List.append(&2, Tr.Ent, pre, [e])
          +b2 = List.append(&2, Tr.Ent, b, [e])
          +ng = pt.or_r(Tr.elem(gone, k), Tr.elem(gone, p), eh)
          +ok1 = pt.ok_keep(pre, b, gone, e <> P, k, p, L.tree.pt.and_l(Tr.ok(pre, k, p), pt.upl(r, pre2), up), cv, ng)
          +c2 = L.tree.pt.and_t(Bool.or(Tr.has(b2, k), Tr.elem(gone, k)), True{}, pt.or_tl(Tr.has(b2, k), Tr.elem(gone, k), pt.has_app_r(b, [e], k, pt.has_head(e, Nil{}))), {==})
          +cv2 = pt.cov_app(pre, [e], b2, gone, pt.cov_b(pre, b, [e], gone, cv), c2)
          +ih = pt.rooted_prune_go(r, gone, Tr.gone.at(r, gone), {==}, pre2, b2, cv2, L.tree.pt.and_r(Tr.ok(pre, k, p), pt.upl(r, pre2), up))
          +eq = pt.app_snoc(b, e, P)
          +rest = Equal.trans(Bool, Tr.rooted.go(P, List.append(&2, Tr.Ent, b, e <> P)), Tr.rooted.go(P, List.append(&2, Tr.Ent, b2, P)), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, l => Tr.rooted.go(P, l), List.append(&2, Tr.Ent, b, e <> P), List.append(&2, Tr.Ent, b2, P), Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, b2, P), List.append(&2, Tr.Ent, b, e <> P), eq)), ih)
          L.tree.pt.and_t(Tr.ok(List.append(&2, Tr.Ent, b, e <> P), k, p), Tr.rooted.go(P, List.append(&2, Tr.Ent, b, e <> P)), ok1, rest)

def pt.del_sound(+t: List<&2, Tr.Ent>, +x: Nat, +st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.prune(t, x)) == True{} : Bool}:
  +R = Tr.prune(t, x)
  +so = L.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), st)
  +ro = L.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), st)
  L.tree.pt.and_t(Tr.sorted(R), Tr.rooted(R), pt.sorted_prune_go(t, [x], Tr.gone.at(t, [x]), so), pt.rooted_prune_go(t, [x], Tr.gone.at(t, [x]), {==}, Nil{}, Nil{}, {==}, pt.upl_of(t, Nil{}, ro, so)))

def pt.keep_sound(+t: List<&2, Tr.Ent>, +n: List<&2, Tr.Ent>, b: Bool, eb: {Tr.sound(n) == b : Bool}, st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.keep.at(b, t, n)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      st

# The journal
# -----------

def apply_sound(+t: List<&2, Tr.Ent>, +good: {Tr.sound(t) == True{} : Bool}, r: Tr.Rec) -> {Tr.sound(Tr.apply(t, r)) == True{} : Bool}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          pt.put_sound(t, k, p, v, Tr.ok(t, k, p), {==}, good)
        case Tr.Del{+x}:
          match x:
            case 0n:
              good
            case 1n+y:
              pt.del_sound(t, 1n+y, good)
    case Tr.Rewind{+ops}:
      pt.keep_sound(t, Tr.patch(ops, t), Tr.sound(Tr.patch(ops, t)), {==}, good)

def pt.go_sound(rs: List<&2, Tr.Rec>, +t: List<&2, Tr.Ent>, +st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.go(rs, t)) == True{} : Bool}:
  match rs:
    case Nil{}:
      st
    case +r <> rest:
      pt.go_sound(rest, Tr.apply(t, r), apply_sound(t, st, r))

def replay_sound(+rs: List<&2, Tr.Rec>) -> {Tr.sound(Tr.replay(rs)) == True{} : Bool}:
  pt.go_sound(rs, Nil{}, {==})

# Keys that differ
# ----------------

def pt.ne_go(+a: Nat, +x: Nat, c: Bool, ec: {Nat.is_eq(a, x) == c : Bool}, -f: Nat -> Bool, na: {f(a) == False{} : Bool}, hx: {f(x) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +fe = Equal.cong(Nat, Bool, f, a, x, pt.eq_true(a, x, ec))
      pt.void({True{} == False{} : Bool}, pt.flip(f(x), hx, Equal.trans(Bool, f(x), f(a), False{}, Equal.sym(Bool, f(a), f(x), fe), na)))
    case False{}:
      {==}

# a key a test rejects is not a key it accepts
def pt.ne_by(+a: Nat, +x: Nat, -f: Nat -> Bool, na: {f(a) == False{} : Bool}, hx: {f(x) == True{} : Bool}) -> {Nat.is_eq(a, x) == False{} : Bool}:
  pt.ne_go(a, x, Nat.is_eq(a, x), {==}, f, na, hx)

def pt.ne_by2(+a: Nat, +x: Nat, -f: Nat -> Bool, ha: {f(a) == True{} : Bool}, nx: {f(x) == False{} : Bool}) -> {Nat.is_eq(a, x) == False{} : Bool}:
  L.pt.ne_comm(x, a, pt.ne_by(x, a, f, nx, ha))

def pt.eq_of(+a: Nat, +b: Nat, ab: {a == b : Nat}) -> {Nat.is_eq(b, a) == True{} : Bool}:
  %ab : {Nat.is_eq(_, a) == True{} : Bool}
  Equal.sym(Bool, True{}, Nat.is_eq(a, a), pt.eq_refl(a))

def pt.val(m: Maybe<&2, Tr.Ent>, d: Tr.Ent) -> Tr.Ent:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def tree.pt.some_inj(+x: Tr.Ent, +y: Tr.Ent, h: {Some{x} == Some{y} : Maybe<&2, Tr.Ent>}) -> {x == y : Tr.Ent}:
  Equal.cong(Maybe<&2, Tr.Ent>, Tr.Ent, m => pt.val(m, x), Some{x}, Some{y}, h)

def pt.get_below(X: List<&2, Tr.Ent>, +y: Nat, +al: {Tr.above(y, X) == True{} : Bool}, +st: {Tr.sorted(X) == True{} : Bool}) -> {Tr.get(X, y) == None{} : Maybe<&2, Tr.Ent>}:
  match X:
    case Nil{}:
      {==}
    case +h <> +r:
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h <> r, y), Tr.get(r, y), None{}, pt.get_miss(h, r, y, L.pt.lt_ne_r(y, Tr.Ent.k(h), al)), pt.get_below(r, y, pt.above_tail(y, h, r, al, st), L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)))

# a node above every node of s does not change what s holds
def pt.within_cons(s: List<&2, Tr.Ent>, +h: Tr.Ent, +r: List<&2, Tr.Ent>, +w: {Tr.within(s, r) == True{} : Bool}, +al: {Tr.above(Tr.Ent.k(h), s) == True{} : Bool}, +st: {Tr.sorted(s) == True{} : Bool}) -> {Tr.within(s, h <> r) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +i = Tr.same(Tr.get(r, Tr.Ent.k(e)), Some{e})
      +gm = pt.get_miss(h, r, Tr.Ent.k(e), L.pt.lt_ne(Tr.Ent.k(h), Tr.Ent.k(e), al))
      +hd = Equal.trans(Bool, Tr.same(Tr.get(h <> r, Tr.Ent.k(e)), Some{e}), i, True{}, Equal.cong(Maybe<&2, Tr.Ent>, Bool, m => Tr.same(m, Some{e}), Tr.get(h <> r, Tr.Ent.k(e)), Tr.get(r, Tr.Ent.k(e)), gm), L.tree.pt.and_l(i, Tr.within(rest, r), w))
      L.tree.pt.and_t(Tr.same(Tr.get(h <> r, Tr.Ent.k(e)), Some{e}), Tr.within(rest, h <> r), hd, pt.within_cons(rest, h, r, L.tree.pt.and_r(i, Tr.within(rest, r), w), pt.above_tail(Tr.Ent.k(h), e, rest, al, st), L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), rest), Tr.sorted(rest), st)))

# a sorted tree holds each of its nodes
def pt.within_self(t: List<&2, Tr.Ent>, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.within(t, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
      +hd = Equal.trans(Bool, Tr.same(Tr.get(h <> r, Tr.Ent.k(h)), Some{h}), Tr.same(Some{h}, Some{h}), True{}, Equal.cong(Maybe<&2, Tr.Ent>, Bool, m => Tr.same(m, Some{h}), Tr.get(h <> r, Tr.Ent.k(h)), Some{h}, pt.get_head(h, r)), pt.same_refl(h))
      L.tree.pt.and_t(Tr.same(Tr.get(h <> r, Tr.Ent.k(h)), Some{h}), Tr.within(r, h <> r), hd, pt.within_cons(r, h, r, pt.within_self(r, sr), L.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st), sr))

# Rewind: still, minimal
# ----------------------

# b has the key of every node of s
def pt.allhas(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Tr.has(b, Tr.Ent.k(e)), pt.allhas(rest, b))

def pt.allhas_cons(s: List<&2, Tr.Ent>, +h: Tr.Ent, +r: List<&2, Tr.Ent>, +ah: {pt.allhas(s, r) == True{} : Bool}) -> {pt.allhas(s, h <> r) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +i = Tr.has(r, Tr.Ent.k(e))
      +hd = Equal.trans(Bool, Tr.has(h <> r, Tr.Ent.k(e)), Bool.or(Nat.is_eq(Tr.Ent.k(h), Tr.Ent.k(e)), i), True{}, pt.has_cons(h, r, Tr.Ent.k(e)), pt.or_tr(Nat.is_eq(Tr.Ent.k(h), Tr.Ent.k(e)), i, L.tree.pt.and_l(i, pt.allhas(rest, r), ah)))
      L.tree.pt.and_t(Tr.has(h <> r, Tr.Ent.k(e)), pt.allhas(rest, h <> r), hd, pt.allhas_cons(rest, h, r, L.tree.pt.and_r(i, pt.allhas(rest, r), ah)))

def pt.allhas_self(t: List<&2, Tr.Ent>) -> {pt.allhas(t, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      L.tree.pt.and_t(Tr.has(h <> r, Tr.Ent.k(h)), pt.allhas(r, h <> r), pt.has_head(h, r), pt.allhas_cons(r, h, r, pt.allhas_self(r)))

# Rewind: reaches
# ---------------
# A lookup after a patch follows the ops on its key (`pt.look`); the dels
# drop exactly the keys b lacks, the puts set exactly the nodes a lacks or
# holds differently. So the patched tree and b agree on every key, and two
# sorted trees that agree on their keys are equal (`pt.ext`).

def tree.pt.pick(c: Bool, n: Maybe<&2, Tr.Ent>, m: Maybe<&2, Tr.Ent>) -> Maybe<&2, Tr.Ent>:
  match c:
    case True{}:
      n
    case False{}:
      m

# the node at key x after one op, from m
def pt.upd(o: Tr.Op, m: Maybe<&2, Tr.Ent>, +x: Nat) -> Maybe<&2, Tr.Ent>:
  match o:
    case Tr.Put{+k, p, v}:
      tree.pt.pick(Nat.is_eq(k, x), Some{Tr.Ent{k, p, v}}, m)
    case Tr.Del{k}:
      tree.pt.pick(Nat.is_eq(k, x), None{}, m)

# the node at key x after the ops, from m
def pt.look(ops: List<&2, Tr.Op>, m: Maybe<&2, Tr.Ent>, +x: Nat) -> Maybe<&2, Tr.Ent>:
  match ops:
    case Nil{}:
      m
    case o <> rest:
      pt.look(rest, pt.upd(o, m, x), x)

def pt.get_put_go(+t: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +v: Nat, +x: Nat, c: Bool, ec: {Nat.is_eq(k, x) == c : Bool}) -> {Tr.get(Tr.set(t, Tr.Ent{k, p, v}), x) == tree.pt.pick(c, Some{Tr.Ent{k, p, v}}, Tr.get(t, x)) : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      %pt.eq_true(k, x, ec) : {Tr.get(Tr.set(t, Tr.Ent{k, p, v}), _) == Some{Tr.Ent{k, p, v}} : Maybe<&2, Tr.Ent>}
      pt.get_set_same(t, Tr.Ent{k, p, v})
    case False{}:
      pt.get_set_other(t, Tr.Ent{k, p, v}, x, ec)

def pt.get_del_go(+t: List<&2, Tr.Ent>, +y: Nat, +x: Nat, c: Bool, ec: {Nat.is_eq(y, x) == c : Bool}) -> {Tr.get(Tr.unset(t, y), x) == tree.pt.pick(c, None{}, Tr.get(t, x)) : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      %pt.eq_true(y, x, ec) : {Tr.get(Tr.unset(t, y), _) == None{} : Maybe<&2, Tr.Ent>}
      pt.get_unset_same(t, y)
    case False{}:
      pt.get_unset_other(t, y, x, ec)

def pt.get_exact(+t: List<&2, Tr.Ent>, o: Tr.Op, +x: Nat) -> {Tr.get(Tr.exact(t, o), x) == pt.upd(o, Tr.get(t, x), x) : Maybe<&2, Tr.Ent>}:
  match o:
    case Tr.Put{+k, +p, +v}:
      pt.get_put_go(t, k, p, v, x, Nat.is_eq(k, x), {==})
    case Tr.Del{+y}:
      pt.get_del_go(t, y, x, Nat.is_eq(y, x), {==})

def pt.get_patch(ops: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>, +x: Nat) -> {Tr.get(Tr.patch(ops, t), x) == pt.look(ops, Tr.get(t, x), x) : Maybe<&2, Tr.Ent>}:
  match ops:
    case Nil{}:
      {==}
    case +o <> +rest:
      +t2 = Tr.exact(t, o)
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(Tr.patch(rest, t2), x), pt.look(rest, Tr.get(t2, x), x), pt.look(rest, pt.upd(o, Tr.get(t, x), x), x), pt.get_patch(rest, t2, x), Equal.cong(Maybe<&2, Tr.Ent>, Maybe<&2, Tr.Ent>, m => pt.look(rest, m, x), Tr.get(t2, x), pt.upd(o, Tr.get(t, x), x), pt.get_exact(t, o, x)))

def pt.look_app(xs: List<&2, Tr.Op>, +ys: List<&2, Tr.Op>, +m: Maybe<&2, Tr.Ent>, +x: Nat) -> {pt.look(List.append(&2, Tr.Op, xs, ys), m, x) == pt.look(ys, pt.look(xs, m, x), x) : Maybe<&2, Tr.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +r:
      pt.look_app(r, ys, pt.upd(o, m, x), x)

def pt.pick_same(c: Bool, +m: Maybe<&2, Tr.Ent>) -> {tree.pt.pick(c, m, m) == m : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def pt.dels_none(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, +x: Nat) -> {pt.look(Tr.dels.go(s, b, hit), None{}, x) == None{} : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          pt.dels_none(r, b, Tr.held.at(r, b), x)
        case False{}:
          +c = Nat.is_eq(Tr.Ent.k(e), x)
          %Equal.sym(Maybe<&2, Tr.Ent>, tree.pt.pick(c, None{}, None{}), None{}, pt.pick_same(c, None{})) : {pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), _, x) == None{} : Maybe<&2, Tr.Ent>}
          pt.dels_none(r, b, Tr.held.at(r, b), x)

# the dels leave a key the target holds
def pt.dels_keep(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.held.at(s, b) == hit : Bool}, +m: Maybe<&2, Tr.Ent>, +x: Nat, +hb: {Tr.has(b, x) == True{} : Bool}) -> {pt.look(Tr.dels.go(s, b, hit), m, x) == m : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          pt.dels_keep(r, b, Tr.held.at(r, b), {==}, m, x, hb)
        case False{}:
          +ne = pt.ne_by(Tr.Ent.k(e), x, z => Tr.has(b, z), eh, hb)
          %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ne) : {pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), tree.pt.pick(_, None{}, m), x) == m : Maybe<&2, Tr.Ent>}
          pt.dels_keep(r, b, Tr.held.at(r, b), {==}, m, x, hb)

def pt.dd_go(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +x: Nat, c: Bool, ec: {Nat.is_eq(Tr.Ent.k(e), x) == c : Bool}, ih: {pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), Tr.get(r, x), x) == None{} : Maybe<&2, Tr.Ent>}) -> {pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), tree.pt.pick(c, None{}, Tr.get(e <> r, x)), x) == None{} : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      pt.dels_none(r, b, Tr.held.at(r, b), x)
    case False{}:
      %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), pt.get_miss(e, r, x, ec)) : {pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), _, x) == None{} : Maybe<&2, Tr.Ent>}
      ih

# the dels drop a key the target lacks
def pt.dels_drop(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.held.at(s, b) == hit : Bool}, +x: Nat, +hb: {Tr.has(b, x) == False{} : Bool}) -> {pt.look(Tr.dels.go(s, b, hit), Tr.get(s, x), x) == None{} : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ne = pt.ne_by2(Tr.Ent.k(e), x, z => Tr.has(b, z), eh, hb)
          %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), pt.get_miss(e, r, x, ne)) : {pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), _, x) == None{} : Maybe<&2, Tr.Ent>}
          pt.dels_drop(r, b, Tr.held.at(r, b), {==}, x, hb)
        case False{}:
          pt.dd_go(e, r, b, x, Nat.is_eq(Tr.Ent.k(e), x), {==}, pt.dels_drop(r, b, Tr.held.at(r, b), {==}, x, hb))

def pt.gnh_go(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, c: Bool, ec: {Nat.is_eq(Tr.Ent.k(e), x) == c : Bool}, gn: {Tr.get(e <> r, x) == None{} : Maybe<&2, Tr.Ent>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      pt.some_none({True{} == False{} : Bool}, e, Equal.trans(Maybe<&2, Tr.Ent>, Some{e}, Tr.get(e <> r, x), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Some{e}, pt.get_hit(e, r, x, ec)), gn))
    case False{}:
      {==}

def pt.get_none_head(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, gn: {Tr.get(e <> r, x) == None{} : Maybe<&2, Tr.Ent>}) -> {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}:
  pt.gnh_go(e, r, x, Nat.is_eq(Tr.Ent.k(e), x), {==}, gn)

# the puts leave a key the target lacks
def pt.puts_miss(+a: List<&2, Tr.Ent>, s: List<&2, Tr.Ent>, hit: Bool, +m: Maybe<&2, Tr.Ent>, +x: Nat, +gn: {Tr.get(s, x) == None{} : Maybe<&2, Tr.Ent>}) -> {pt.look(Tr.puts.go(a, s, hit), m, x) == m : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ne = pt.get_none_head(e, r, x, gn)
          pt.puts_miss(a, r, Tr.kept.at(a, r), m, x, Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r, x), Tr.get(e <> r, x), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), pt.get_miss(e, r, x, ne)), gn))
        case False{}:
          +ne = pt.get_none_head(e, r, x, gn)
          %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ne) : {pt.look(Tr.puts.go(a, r, Tr.kept.at(a, r)), tree.pt.pick(_, Some{Tr.Ent{Tr.Ent.k(e), Tr.Ent.p(e), Tr.Ent.v(e)}}, m), x) == m : Maybe<&2, Tr.Ent>}
          pt.puts_miss(a, r, Tr.kept.at(a, r), m, x, Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r, x), Tr.get(e <> r, x), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), pt.get_miss(e, r, x, ne)), gn))

def pt.ph_go(+a: List<&2, Tr.Ent>, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +m: Maybe<&2, Tr.Ent>, +x: Nat, +z: Tr.Ent, c: Bool, +ec: {Nat.is_eq(Tr.Ent.k(e), x) == c : Bool}, hit: Bool, eh: {Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e}) == hit : Bool}, +al: {Tr.above(Tr.Ent.k(e), r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}, ih: {Tr.get(r, x) == Some{z} : Maybe<&2, Tr.Ent>} -> {pt.look(Tr.puts.go(a, r, Tr.kept.at(a, r)), m, x) == tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}, +gs: {Tr.get(e <> r, x) == Some{z} : Maybe<&2, Tr.Ent>}) -> {pt.look(Tr.puts.go(a, e <> r, hit), m, x) == tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}:
  match c hit:
    case True{} True{}:
      +P = Tr.puts.go(a, r, Tr.kept.at(a, r))
      +ez = tree.pt.some_inj(e, z, Equal.trans(Maybe<&2, Tr.Ent>, Some{e}, Tr.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Some{e}, pt.get_hit(e, r, x, ec)), gs))
      %ez : {pt.look(P, m, x) == tree.pt.pick(Tr.same(Tr.get(a, x), Some{_}), m, Some{_}) : Maybe<&2, Tr.Ent>}
      %pt.eq_true(Tr.Ent.k(e), x, ec) : {pt.look(P, m, _) == tree.pt.pick(Tr.same(Tr.get(a, _), Some{e}), m, Some{e}) : Maybe<&2, Tr.Ent>}
      %Equal.sym(Bool, Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e}), True{}, eh) : {pt.look(P, m, Tr.Ent.k(e)) == tree.pt.pick(_, m, Some{e}) : Maybe<&2, Tr.Ent>}
      pt.puts_miss(a, r, Tr.kept.at(a, r), m, Tr.Ent.k(e), pt.get_below(r, Tr.Ent.k(e), al, sr))
    case True{} False{}:
      +P = Tr.puts.go(a, r, Tr.kept.at(a, r))
      +E = {Tr.Ent{Tr.Ent.k(e), Tr.Ent.p(e), Tr.Ent.v(e)} : Tr.Ent}
      +ez = tree.pt.some_inj(e, z, Equal.trans(Maybe<&2, Tr.Ent>, Some{e}, Tr.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Some{e}, pt.get_hit(e, r, x, ec)), gs))
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), True{}, ec) : {pt.look(P, tree.pt.pick(_, Some{E}, m), x) == tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}
      %ez : {pt.look(P, Some{E}, x) == tree.pt.pick(Tr.same(Tr.get(a, x), Some{_}), m, Some{_}) : Maybe<&2, Tr.Ent>}
      %pt.eq_true(Tr.Ent.k(e), x, ec) : {pt.look(P, Some{E}, _) == tree.pt.pick(Tr.same(Tr.get(a, _), Some{e}), m, Some{e}) : Maybe<&2, Tr.Ent>}
      %Equal.sym(Bool, Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e}), False{}, eh) : {pt.look(P, Some{E}, Tr.Ent.k(e)) == tree.pt.pick(_, m, Some{e}) : Maybe<&2, Tr.Ent>}
      Equal.trans(Maybe<&2, Tr.Ent>, pt.look(P, Some{E}, Tr.Ent.k(e)), Some{E}, Some{e}, pt.puts_miss(a, r, Tr.kept.at(a, r), Some{E}, Tr.Ent.k(e), pt.get_below(r, Tr.Ent.k(e), al, sr)), Equal.cong(Tr.Ent, Maybe<&2, Tr.Ent>, y => Some{y}, E, e, pt.ent_eta(e)))
    case False{} True{}:
      ih(Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r, x), Tr.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), pt.get_miss(e, r, x, ec)), gs))
    case False{} False{}:
      +P = Tr.puts.go(a, r, Tr.kept.at(a, r))
      +E = {Tr.Ent{Tr.Ent.k(e), Tr.Ent.p(e), Tr.Ent.v(e)} : Tr.Ent}
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ec) : {pt.look(P, tree.pt.pick(_, Some{E}, m), x) == tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}
      ih(Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r, x), Tr.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), pt.get_miss(e, r, x, ec)), gs))

# the puts set a key the target holds, unless a holds it the same
def pt.puts_hit(+a: List<&2, Tr.Ent>, s: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.kept.at(a, s) == hit : Bool}, +m: Maybe<&2, Tr.Ent>, +x: Nat, +z: Tr.Ent, +st: {Tr.sorted(s) == True{} : Bool}) -> {Tr.get(s, x) == Some{z} : Maybe<&2, Tr.Ent>} -> {pt.look(Tr.puts.go(a, s, hit), m, x) == tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      gs => tree.pt.none_some({pt.look(Tr.puts.go(a, Nil{}, hit), m, x) == tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}, z, gs)
    case +e <> +r:
      ih = pt.puts_hit(a, r, Tr.kept.at(a, r), {==}, m, x, z, L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st))
      gs => pt.ph_go(a, e, r, m, x, z, Nat.is_eq(Tr.Ent.k(e), x), {==}, hit, eh, L.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st), L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st), ih, gs)

def pt.reach_tail(+a: List<&2, Tr.Ent>, +x: Nat, +z: Tr.Ent, c: Bool, ec: {Tr.same(Tr.get(a, x), Some{z}) == c : Bool}) -> {tree.pt.pick(c, Tr.get(a, x), Some{z}) == Some{z} : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      pt.same_some(Tr.get(a, x), z, ec)
    case False{}:
      {==}

def pt.reach_go(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +x: Nat, +sb: {Tr.sorted(b) == True{} : Bool}, mb: Maybe<&2, Tr.Ent>, +eb: {Tr.get(b, x) == mb : Maybe<&2, Tr.Ent>}) -> {pt.look(Tr.puts.go(a, b, Tr.kept.at(a, b)), pt.look(Tr.dels.go(a, b, Tr.held.at(a, b)), Tr.get(a, x), x), x) == Tr.get(b, x) : Maybe<&2, Tr.Ent>}:
  match mb:
    case None{}:
      +P = Tr.puts.go(a, b, Tr.kept.at(a, b))
      +D = Tr.dels.go(a, b, Tr.held.at(a, b))
      +hb = Equal.cong(Maybe<&2, Tr.Ent>, Bool, mm => Maybe.is_some(&2, Tr.Ent, mm), Tr.get(b, x), None{}, eb)
      %Equal.sym(Maybe<&2, Tr.Ent>, pt.look(D, Tr.get(a, x), x), None{}, pt.dels_drop(a, b, Tr.held.at(a, b), {==}, x, hb)) : {pt.look(P, _, x) == Tr.get(b, x) : Maybe<&2, Tr.Ent>}
      Equal.trans(Maybe<&2, Tr.Ent>, pt.look(P, None{}, x), None{}, Tr.get(b, x), pt.puts_miss(a, b, Tr.kept.at(a, b), None{}, x, eb), Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(b, x), None{}, eb))
    case Some{+z}:
      +P = Tr.puts.go(a, b, Tr.kept.at(a, b))
      +D = Tr.dels.go(a, b, Tr.held.at(a, b))
      +ga = Tr.get(a, x)
      +hb = Equal.cong(Maybe<&2, Tr.Ent>, Bool, mm => Maybe.is_some(&2, Tr.Ent, mm), Tr.get(b, x), Some{z}, eb)
      %Equal.sym(Maybe<&2, Tr.Ent>, pt.look(D, ga, x), ga, pt.dels_keep(a, b, Tr.held.at(a, b), {==}, ga, x, hb)) : {pt.look(P, _, x) == Tr.get(b, x) : Maybe<&2, Tr.Ent>}
      +c = Tr.same(ga, Some{z})
      Equal.trans(Maybe<&2, Tr.Ent>, pt.look(P, ga, x), tree.pt.pick(c, ga, Some{z}), Tr.get(b, x), pt.puts_hit(a, b, Tr.kept.at(a, b), {==}, ga, x, z, sb)(eb), Equal.trans(Maybe<&2, Tr.Ent>, tree.pt.pick(c, ga, Some{z}), Some{z}, Tr.get(b, x), pt.reach_tail(a, x, z, c, {==}), Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(b, x), Some{z}, eb)))

# after the rewind ops, the tree holds at x what the target holds
def pt.reach_at(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +x: Nat, +sb: {Tr.sorted(b) == True{} : Bool}) -> {Tr.get(Tr.patch(Tr.diff(a, b), a), x) == Tr.get(b, x) : Maybe<&2, Tr.Ent>}:
  +D = Tr.dels(a, b)
  +P = Tr.puts(a, b)
  +ga = Tr.get(a, x)
  Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(Tr.patch(Tr.diff(a, b), a), x), pt.look(List.append(&2, Tr.Op, D, P), ga, x), Tr.get(b, x), pt.get_patch(Tr.diff(a, b), a, x), Equal.trans(Maybe<&2, Tr.Ent>, pt.look(List.append(&2, Tr.Op, D, P), ga, x), pt.look(P, pt.look(D, ga, x), x), Tr.get(b, x), pt.look_app(D, P, ga, x), pt.reach_go(a, b, x, sb, Tr.get(b, x), {==})))

# l1 and l2 hold the same node at the key of each node of es
def pt.Agree(es: List<&2, Tr.Ent>, +l1: List<&2, Tr.Ent>, +l2: List<&2, Tr.Ent>) -> Type:
  match es:
    case Nil{}:
      Unit
    case +e <> rest:
      ({Tr.get(l1, Tr.Ent.k(e)) == Tr.get(l2, Tr.Ent.k(e)) : Maybe<&2, Tr.Ent>} & pt.Agree(rest, l1, l2))

def pt.agree_reach(es: List<&2, Tr.Ent>, +a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +sb: {Tr.sorted(b) == True{} : Bool}) -> pt.Agree(es, Tr.patch(Tr.diff(a, b), a), b):
  match es:
    case Nil{}:
      Unit{}
    case +e <> rest:
      (pt.reach_at(a, b, Tr.Ent.k(e), sb), pt.agree_reach(rest, a, b, sb))

# below two heads with one key, the lists agree as they did
def pt.agree_strip(es: List<&2, Tr.Ent>, +h1: Tr.Ent, +r1: List<&2, Tr.Ent>, +h2: Tr.Ent, +r2: List<&2, Tr.Ent>, ag: pt.Agree(es, h1 <> r1, h2 <> r2), +al: {Tr.above(Tr.Ent.k(h1), es) == True{} : Bool}, +st: {Tr.sorted(es) == True{} : Bool}, +keq: {Tr.Ent.k(h1) == Tr.Ent.k(h2) : Nat}) -> pt.Agree(es, r1, r2):
  match es:
    case Nil{}:
      Unit{}
    case +e <> +rest:
      (eq0, agt) = ag
      +k = Tr.Ent.k(e)
      +ne1 = L.pt.lt_ne(Tr.Ent.k(h1), k, al)
      +ne2 = pt.ne_at(Tr.Ent.k(h2), Tr.Ent.k(h1), k, Equal.sym(Nat, Tr.Ent.k(h1), Tr.Ent.k(h2), keq), ne1)
      +hd = Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r1, k), Tr.get(h1 <> r1, k), Tr.get(r2, k), Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, k), Tr.get(r1, k), pt.get_miss(h1, r1, k, ne1)), Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, k), Tr.get(h2 <> r2, k), Tr.get(r2, k), eq0, pt.get_miss(h2, r2, k, ne2)))
      (hd, pt.agree_strip(rest, h1, r1, h2, r2, agt, pt.above_tail(Tr.Ent.k(h1), e, rest, al, st), L.tree.pt.and_r(Tr.above(k, rest), Tr.sorted(rest), st), keq))

# two sorted lists that agree have the same first key
def pt.ext_head(+h1: Tr.Ent, +r1: List<&2, Tr.Ent>, +h2: Tr.Ent, +r2: List<&2, Tr.Ent>, c: Cmp, ec: {Nat.cmp(Tr.Ent.k(h1), Tr.Ent.k(h2)) == c : Cmp}, e1: {Tr.get(h1 <> r1, Tr.Ent.k(h1)) == Tr.get(h2 <> r2, Tr.Ent.k(h1)) : Maybe<&2, Tr.Ent>}, e2: {Tr.get(h1 <> r1, Tr.Ent.k(h2)) == Tr.get(h2 <> r2, Tr.Ent.k(h2)) : Maybe<&2, Tr.Ent>}, +s1: {Tr.sorted(h1 <> r1) == True{} : Bool}, +s2: {Tr.sorted(h2 <> r2) == True{} : Bool}) -> {Tr.Ent.k(h1) == Tr.Ent.k(h2) : Nat}:
  match c:
    case LT{}:
      +gn = pt.get_below(h2 <> r2, Tr.Ent.k(h1), pt.cmp_lt(Tr.Ent.k(h1), Tr.Ent.k(h2), ec), s2)
      pt.some_none({Tr.Ent.k(h1) == Tr.Ent.k(h2) : Nat}, h1, Equal.trans(Maybe<&2, Tr.Ent>, Some{h1}, Tr.get(h1 <> r1, Tr.Ent.k(h1)), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h1}, pt.get_head(h1, r1)), Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Tr.get(h2 <> r2, Tr.Ent.k(h1)), None{}, e1, gn)))
    case EQ{}:
      pt.cmp_eq(Tr.Ent.k(h1), Tr.Ent.k(h2), ec)
    case GT{}:
      +gn = pt.get_below(h1 <> r1, Tr.Ent.k(h2), pt.cmp_gt(Tr.Ent.k(h1), Tr.Ent.k(h2), ec), s1)
      tree.pt.none_some({Tr.Ent.k(h1) == Tr.Ent.k(h2) : Nat}, h2, Equal.trans(Maybe<&2, Tr.Ent>, None{}, Tr.get(h1 <> r1, Tr.Ent.k(h2)), Some{h2}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h2)), None{}, gn), Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h2)), Tr.get(h2 <> r2, Tr.Ent.k(h2)), Some{h2}, e2, pt.get_head(h2, r2))))

# two sorted lists that agree on their keys are equal
def pt.ext(l1: List<&2, Tr.Ent>, l2: List<&2, Tr.Ent>, +s1: {Tr.sorted(l1) == True{} : Bool}, +s2: {Tr.sorted(l2) == True{} : Bool}, A1: pt.Agree(l1, l1, l2), A2: pt.Agree(l2, l1, l2)) -> {l1 == l2 : List<&2, Tr.Ent>}:
  match l1 l2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+h2, +r2}:
      (e2, t2) = A2
      tree.pt.none_some({Nil{} == h2 <> r2 : List<&2, Tr.Ent>}, h2, Equal.trans(Maybe<&2, Tr.Ent>, None{}, Tr.get(h2 <> r2, Tr.Ent.k(h2)), Some{h2}, e2, pt.get_head(h2, r2)))
    case Con{+h1, +r1} Nil{}:
      (e1, t1) = A1
      pt.some_none({h1 <> r1 == Nil{} : List<&2, Tr.Ent>}, h1, Equal.trans(Maybe<&2, Tr.Ent>, Some{h1}, Tr.get(h1 <> r1, Tr.Ent.k(h1)), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h1}, pt.get_head(h1, r1)), e1))
    case Con{+h1, +r1} Con{+h2, +r2}:
      (+e1, t1) = A1
      (+e2, t2) = A2
      +keq = pt.ext_head(h1, r1, h2, r2, Nat.cmp(Tr.Ent.k(h1), Tr.Ent.k(h2)), {==}, e1, e2, s1, s2)
      +s1t = L.tree.pt.and_r(Tr.above(Tr.Ent.k(h1), r1), Tr.sorted(r1), s1)
      +s2t = L.tree.pt.and_r(Tr.above(Tr.Ent.k(h2), r2), Tr.sorted(r2), s2)
      +al1 = L.tree.pt.and_l(Tr.above(Tr.Ent.k(h1), r1), Tr.sorted(r1), s1)
      +al2 = Equal.trans(Bool, Tr.above(Tr.Ent.k(h1), r2), Tr.above(Tr.Ent.k(h2), r2), True{}, Equal.cong(Nat, Bool, n => Tr.above(n, r2), Tr.Ent.k(h1), Tr.Ent.k(h2), keq), L.tree.pt.and_l(Tr.above(Tr.Ent.k(h2), r2), Tr.sorted(r2), s2))
      +ih = pt.ext(r1, r2, s1t, s2t, pt.agree_strip(r1, h1, r1, h2, r2, t1, al1, s1t, keq), pt.agree_strip(r2, h1, r1, h2, r2, t2, al2, s2t, keq))
      +hs = Equal.trans(Maybe<&2, Tr.Ent>, Some{h1}, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h2}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h1}, pt.get_head(h1, r1)), Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Tr.get(h2 <> r2, Tr.Ent.k(h1)), Some{h2}, e1, pt.get_hit(h2, r2, Tr.Ent.k(h1), pt.eq_of(Tr.Ent.k(h1), Tr.Ent.k(h2), keq))))
      %tree.pt.some_inj(h1, h2, hs) : {h1 <> r1 == _ <> r2 : List<&2, Tr.Ent>}
      %ih : {h1 <> r1 == h1 <> _ : List<&2, Tr.Ent>}
      {==}

def rewind_reaches(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, ga: {Tr.sound(a) == True{} : Bool}, +gb: {Tr.sound(b) == True{} : Bool}) -> {Tr.apply(a, Tr.Rewind{Tr.diff(a, b)}) == b : List<&2, Tr.Ent>}:
  +n = Tr.patch(Tr.diff(a, b), a)
  +sb = L.tree.pt.and_l(Tr.sorted(b), Tr.rooted(b), gb)
  +sn = pt.sorted_patch(Tr.diff(a, b), a, L.tree.pt.and_l(Tr.sorted(a), Tr.rooted(a), ga))
  +eq = pt.ext(n, b, sn, sb, pt.agree_reach(n, a, b, sb), pt.agree_reach(b, a, b, sb))
  %Equal.sym(List<&2, Tr.Ent>, n, b, eq) : {Tr.keep.at(Tr.sound(_), a, _) == b : List<&2, Tr.Ent>}
  %Equal.sym(Bool, Tr.sound(b), True{}, gb) : {Tr.keep.at(_, a, b) == b : List<&2, Tr.Ent>}
  {==}

def pt.or_above_tail(c: Bool, +g: Nat, +e: Tr.Ent, +r: List<&2, Tr.Ent>, h: {Bool.or(c, Tr.above(g, e <> r)) == True{} : Bool}, +st: {Tr.sorted(e <> r) == True{} : Bool}) -> {Bool.or(c, Tr.above(g, r)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pt.above_tail(g, e, r, h, st)

def pt.above_lt(+a: Nat, +b: Nat, r: List<&2, Tr.Ent>, ab: {Nat.is_lt(a, b) == True{} : Bool}, br: {Tr.above(b, r) == True{} : Bool}) -> {Tr.above(a, r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +h <> +rest:
      pt.lt_trans(a, b, Tr.Ent.k(h), ab, br)

# The compiled core
# -----------------
# The key map refines the sorted list: a fork's left keys are below its
# split and its right keys at or above it (`tc.bst`), so its nodes in
# order are sorted (`tc.sorted_read`), a lookup down the map is the list
# lookup (`tc.get`), and a put, an unset and a drop are the list's set,
# unset and unset of each key (`tc.put_read`, `tc.unset_read`). A record
# on the map is apply on the list (`tc.rec_read`), with the model's answer
# (`tc.rec_ans`); a delete walks only the nodes from its key on, and the
# nodes before them never go (`tc.drops_ge`). The plan merges two sorted
# lists; the merge is diff (`tc.diff_m`).

# the keys of the nodes that prune.go removes from s, in order: the walk
# of a delete with its gone keys as a list (the core keeps them in a key
# map, `Tr.drops.s`; `tc.drops` shows the two walks drop the same keys)
def tc.dgo(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +e <> +rest:
      match hit:
        case True{}:
          Tr.Ent.k(e) <> tc.dgo(rest, Tr.Ent.k(e) <> gone, Tr.gone.at(rest, Tr.Ent.k(e) <> gone))
        case False{}:
          tc.dgo(rest, gone, Tr.gone.at(rest, gone))

def tc.app_assoc(a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +c: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, a, b), c) == List.append(&2, Tr.Ent, a, List.append(&2, Tr.Ent, b, c)) : List<&2, Tr.Ent>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => h <> ys, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, t, b), c), List.append(&2, Tr.Ent, t, List.append(&2, Tr.Ent, b, c)), tc.app_assoc(t, b, c))

def tc.above_app(+k: Nat, r: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +lk: {Nat.is_lt(k, b) == True{} : Bool}, +gb: {L.tc.ge(B, b) == True{} : Bool}) -> {Tr.above(k, List.append(&2, Tr.Ent, r, B)) == True{} : Bool}:
  match r:
    case Nil{}:
      match B:
        case Nil{}:
          {==}
        case +f <> s:
          L.tc.lt_le(k, b, Tr.Ent.k(f), lk, L.tc.ge_head(f, s, b, gb))
    case f <> s:
      ar

def tc.sorted_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +sa: {Tr.sorted(A) == True{} : Bool}, +sb: {Tr.sorted(B) == True{} : Bool}, +la: {L.tc.lt(A, b) == True{} : Bool}, +gb: {L.tc.ge(B, b) == True{} : Bool}) -> {Tr.sorted(List.append(&2, Tr.Ent, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      sb
    case +e <> +r:
      +ar = L.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +R = List.append(&2, Tr.Ent, r, B)
      L.tree.pt.and_t(Tr.above(Tr.Ent.k(e), R), Tr.sorted(R), tc.above_app(Tr.Ent.k(e), r, B, b, ar, L.tc.lt_head(e, r, b, la), gb), tc.sorted_app(r, B, b, sr, sb, L.tc.lt_tail(e, r, b, la), gb))

def tc.get_app_r(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +la: {L.tc.lt(A, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {Tr.get(List.append(&2, Tr.Ent, A, B), x) == Tr.get(B, x) : Maybe<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +e <> +r:
      +R = List.append(&2, Tr.Ent, r, B)
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(e <> R, x), Tr.get(R, x), Tr.get(B, x), pt.get_miss(e, R, x, L.tc.lt_miss(e, b, x, L.tc.lt_head(e, r, b, la), xb)), tc.get_app_r(r, B, b, x, L.tc.lt_tail(e, r, b, la), xb))

def tc.get_none_ge(B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {L.tc.ge(B, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Tr.get(B, x) == None{} : Maybe<&2, Tr.Ent>}:
  match B:
    case Nil{}:
      {==}
    case +f <> +r:
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(f <> r, x), Tr.get(r, x), None{}, pt.get_miss(f, r, x, L.tc.ge_miss(f, b, x, L.tc.ge_head(f, r, b, gb), xb)), tc.get_none_ge(r, b, x, L.tc.ge_tail(f, r, b, gb), xb))

def tc.get_app_l(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {L.tc.ge(B, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Tr.get(List.append(&2, Tr.Ent, A, B), x) == Tr.get(A, x) : Maybe<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      tc.get_none_ge(B, b, x, gb, xb)
    case +e <> +r:
      pt.get_cons_cong(e, List.append(&2, Tr.Ent, r, B), r, x, tc.get_app_l(r, B, b, x, gb, xb))

# The key map: order, lookup, put, unset

def tc.sorted_read(m: Tr.KMap, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.sorted(Tr.KMap.read(m)) == True{} : Bool}:
  match m:
    case Tr.KNil{}:
      {==}
    case Tr.KOne{e}:
      {==}
    case Tr.KFork{+mid, +mp, +l, +r}:
      tc.sorted_app(Tr.KMap.read(l), Tr.KMap.read(r), mid, tc.sorted_read(l, L.tc.bst_l(mid, mp, l, r, bt)), tc.sorted_read(r, L.tc.bst_r(mid, mp, l, r, bt)), L.tc.bst_lt(mid, mp, l, r, bt), L.tc.bst_ge(mid, mp, l, r, bt))

def tc.get_go(m: Tr.KMap, +x: Nat, b: Bool, +eb: {Tr.KMap.at(m, x) == b : Bool}, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.get.go(m, x, b) == Tr.get(Tr.KMap.read(m), x) : Maybe<&2, Tr.Ent>}:
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
      +ih = tc.get_go(l, x, Tr.KMap.at(l, x), {==}, L.tc.bst_l(mid, mp, l, r, bt))
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.KMap.get(l, x), Tr.get(Tr.KMap.read(l), x), Tr.get(List.append(&2, Tr.Ent, Tr.KMap.read(l), Tr.KMap.read(r)), x), ih, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(List.append(&2, Tr.Ent, Tr.KMap.read(l), Tr.KMap.read(r)), x), Tr.get(Tr.KMap.read(l), x), tc.get_app_l(Tr.KMap.read(l), Tr.KMap.read(r), mid, x, L.tc.bst_ge(mid, mp, l, r, bt), eb)))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +ih = tc.get_go(r, x, Tr.KMap.at(r, x), {==}, L.tc.bst_r(mid, mp, l, r, bt))
      Equal.trans(Maybe<&2, Tr.Ent>, Tr.KMap.get(r, x), Tr.get(Tr.KMap.read(r), x), Tr.get(List.append(&2, Tr.Ent, Tr.KMap.read(l), Tr.KMap.read(r)), x), ih, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(List.append(&2, Tr.Ent, Tr.KMap.read(l), Tr.KMap.read(r)), x), Tr.get(Tr.KMap.read(r), x), tc.get_app_r(Tr.KMap.read(l), Tr.KMap.read(r), mid, x, L.tc.bst_lt(mid, mp, l, r, bt), eb)))

# a lookup down the map is the lookup in its nodes
def tc.get(+m: Tr.KMap, +x: Nat, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.get(m, x) == Tr.get(Tr.KMap.read(m), x) : Maybe<&2, Tr.Ent>}:
  tc.get_go(m, x, Tr.KMap.at(m, x), {==}, bt)

def tc.has(+m: Tr.KMap, +x: Nat, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.has(m, x) == Tr.has(Tr.KMap.read(m), x) : Bool}:
  Equal.cong(Maybe<&2, Tr.Ent>, Bool, y => Maybe.is_some(&2, Tr.Ent, y), Tr.KMap.get(m, x), Tr.get(Tr.KMap.read(m), x), tc.get(m, x, bt))

# the entry points

def tc.set_read(+m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.set(m, hs, e)) == Tr.set(Tr.KMap.read(m), e) : List<&2, Tr.Ent>}:
  L.tc.put_read(m, hs, 0n, e, Tr.KMap.at(m, Tr.Ent.k(e)), {==}, bt)

def tc.del_read(+m: Tr.KMap, +x: Nat, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.del(m, x)) == Tr.unset(Tr.KMap.read(m), x) : List<&2, Tr.Ent>}:
  L.tc.unset_read(m, x, Tr.KMap.at(m, x), {==}, bt)

# t less the nodes of keys ks, one by one
def tc.unsets(ks: List<&2, Nat>, t: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match ks:
    case Nil{}:
      t
    case k <> rest:
      tc.unsets(rest, Tr.unset(t, k))

def tc.drop_read(ks: List<&2, Nat>, +m: Tr.KMap, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.drop(ks, m)) == tc.unsets(ks, Tr.KMap.read(m)) : List<&2, Tr.Ent>}:
  match ks:
    case Nil{}:
      {==}
    case +k <> rest:
      +D = Tr.KMap.del(m, k)
      +ih = tc.drop_read(rest, D, L.tc.del_bst(m, k, bt))
      %tc.del_read(m, k, bt) : {Tr.KMap.read(Tr.KMap.drop(rest, D)) == tc.unsets(rest, _) : List<&2, Tr.Ent>}
      ih

# Delete

# every key of gone is x or more
def tc.nall(gone: List<&2, Nat>, +x: Nat) -> Bool:
  match gone:
    case Nil{}:
      True{}
    case +g <> rest:
      Bool.and(Bool.not(Nat.is_lt(g, x)), tc.nall(rest, x))

def tc.elem_none(gone: List<&2, Nat>, +x: Nat, +y: Nat, +ng: {tc.nall(gone, x) == True{} : Bool}, +yx: {Nat.is_lt(y, x) == True{} : Bool}) -> {Tr.elem(gone, y) == False{} : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +g <> +rest:
      +gx = L.pt.not_f(Nat.is_lt(g, x), L.tree.pt.and_l(Bool.not(Nat.is_lt(g, x)), tc.nall(rest, x), ng))
      +ne = L.pt.lt_ne_r(y, g, L.tc.lt_le(y, x, g, yx, gx))
      %Equal.sym(Bool, Nat.is_eq(g, y), False{}, ne) : {Bool.or(_, Tr.elem(rest, y)) == False{} : Bool}
      tc.elem_none(rest, x, y, L.tree.pt.and_r(Bool.not(Nat.is_lt(g, x)), tc.nall(rest, x), ng), yx)

# every node of s is above its parent
def tc.desc(s: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), tc.desc(rest))

def tc.desc_of(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +rs: {Tr.rooted.go(s, all) == True{} : Bool}) -> {tc.desc(s) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +o = L.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(rest, all), rs)
      +lt = L.tree.pt.and_l(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), Bool.or(Nat.is_eq(Tr.Ent.p(e), 0n), Tr.has(all, Tr.Ent.p(e))), o)
      L.tree.pt.and_t(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), tc.desc(rest), lt, tc.desc_of(rest, all, L.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(rest, all), rs)))

def tc.or_ff(a: Bool, b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      L.pt.absurd({Bool.or(True{}, b) == False{} : Bool}, ha)
    case False{}:
      hb

def tc.nall_cons(+k: Nat, +gone: List<&2, Nat>, +x: Nat, +kx: {Nat.is_lt(k, x) == False{} : Bool}, +ng: {tc.nall(gone, x) == True{} : Bool}) -> {tc.nall(k <> gone, x) == True{} : Bool}:
  L.tree.pt.and_t(Bool.not(Nat.is_lt(k, x)), tc.nall(gone, x), L.pt.not_t(Nat.is_lt(k, x), kx), ng)

def tc.dg_ge(hit: Bool, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +X: List<&2, Tr.Ent>, +gone: List<&2, Nat>, +ih1: {tc.dgo(r, gone, Tr.gone.at(r, gone)) == tc.dgo(X, gone, Tr.gone.at(X, gone)) : List<&2, Nat>}, ih2: {tc.dgo(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone)) == tc.dgo(X, Tr.Ent.k(e) <> gone, Tr.gone.at(X, Tr.Ent.k(e) <> gone)) : List<&2, Nat>}) -> {tc.dgo(e <> r, gone, hit) == tc.dgo(e <> X, gone, hit) : List<&2, Nat>}:
  match hit:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, ys => Tr.Ent.k(e) <> ys, tc.dgo(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone)), tc.dgo(X, Tr.Ent.k(e) <> gone, Tr.gone.at(X, Tr.Ent.k(e) <> gone)), ih2)
    case False{}:
      ih1

# The largest parent key of a fork

def tc.ge_trans(a: Nat, b: Nat, c: Nat, +ab: {Nat.is_ge(a, b) == True{} : Bool}, +bc: {Nat.is_ge(b, c) == True{} : Bool}) -> {Nat.is_ge(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      L.pt.absurd({Nat.is_ge(0n, 1n+r) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bc))
    case 0n 1n+q _:
      L.pt.absurd({Nat.is_ge(0n, c) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, ab))
    case 1n+p _ 0n:
      {==}
    case 1n+p 0n 1n+r:
      L.pt.absurd({Nat.is_ge(1n+p, 1n+r) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bc))
    case 1n+p 1n+q 1n+r:
      tc.ge_trans(p, q, r, ab, bc)

# b at or above p and below x: p is below x
def tc.ge_lt(b: Nat, p: Nat, x: Nat, +bp: {Nat.is_ge(b, p) == True{} : Bool}, +bx: {Nat.is_lt(b, x) == True{} : Bool}) -> {Nat.is_lt(p, x) == True{} : Bool}:
  match b p x:
    case _ _ 0n:
      L.tree.pt.absurdF({Nat.is_lt(p, 0n) == True{} : Bool}, bx)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 1n+r:
      L.pt.absurd({Nat.is_lt(1n+q, 1n+r) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bp))
    case 1n+a 0n 1n+r:
      {==}
    case 1n+a 1n+q 1n+r:
      tc.ge_lt(a, q, r, bp, bx)

# every fork's largest parent key is at least each side's
def tc.mpok(m: Tr.KMap) -> Bool:
  match m:
    case Tr.KNil{}:
      True{}
    case Tr.KOne{e}:
      True{}
    case Tr.KFork{+mid, +mp, +l, +r}:
      Bool.and(tc.mpok(l), Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))))

def tc.mpok_rest(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))) == True{} : Bool}:
  L.tree.pt.and_r(tc.mpok(l), Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))), h)

def tc.mpok_l(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {tc.mpok(l) == True{} : Bool}:
  L.tree.pt.and_l(tc.mpok(l), Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))), h)

def tc.mpok_r(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {tc.mpok(r) == True{} : Bool}:
  L.tree.pt.and_l(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r))), tc.mpok_rest(mid, mp, l, r, h))

def tc.mpok_gl(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Nat.is_ge(mp, Tr.KMap.mp(l)) == True{} : Bool}:
  +h2 = L.tree.pt.and_r(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r))), tc.mpok_rest(mid, mp, l, r, h))
  L.tree.pt.and_l(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)), h2)

def tc.mpok_gr(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Nat.is_ge(mp, Tr.KMap.mp(r)) == True{} : Bool}:
  +h2 = L.tree.pt.and_r(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r))), tc.mpok_rest(mid, mp, l, r, h))
  L.tree.pt.and_r(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)), h2)

def tc.mpok_fork(+mid: Nat, +l: Tr.KMap, +r: Tr.KMap, +ml: {tc.mpok(l) == True{} : Bool}, +mr: {tc.mpok(r) == True{} : Bool}) -> {tc.mpok(Tr.KMap.fork(mid, l, r)) == True{} : Bool}:
  +a = Tr.KMap.mp(l)
  +b = Tr.KMap.mp(r)
  +M = Nat.max(a, b)
  L.tree.pt.and_t(tc.mpok(l), Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(M, a), Nat.is_ge(M, b))), ml, L.tree.pt.and_t(tc.mpok(r), Bool.and(Nat.is_ge(M, a), Nat.is_ge(M, b)), mr, L.tree.pt.and_t(Nat.is_ge(M, a), Nat.is_ge(M, b), Nat.max_ge_l(a, b), Nat.max_ge_r(a, b))))

def tc.split_mpok(+a: Tr.Ent, +b: Tr.Ent, c: Bool) -> {tc.mpok(Tr.KMap.split(a, b, c)) == True{} : Bool}:
  match c:
    case True{}:
      tc.mpok_fork(Tr.Ent.k(b), Tr.KOne{a}, Tr.KOne{b}, {==}, {==})
    case False{}:
      tc.mpok_fork(Tr.Ent.k(a), Tr.KOne{b}, Tr.KOne{a}, {==}, {==})

def tc.two_mpok(hs: List<&2, Nat>, +lo: Nat, +a: Tr.Ent, +b: Tr.Ent, ca: Bool, cb: Bool) -> {tc.mpok(Tr.KMap.two(hs, lo, a, b, ca, cb)) == True{} : Bool}:
  match hs:
    case Nil{}:
      tc.split_mpok(a, b, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)))
    case +h <> +rest:
      match ca cb:
        case True{} True{}:
          +g = Tr.KMap.half(rest)
          +X = Tr.KMap.two(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)))
          tc.mpok_fork(Nat.add(lo, h), X, Tr.KNil{}, tc.two_mpok(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g))), {==})
        case True{} False{}:
          tc.mpok_fork(Nat.add(lo, h), Tr.KOne{a}, Tr.KOne{b}, {==}, {==})
        case False{} True{}:
          tc.mpok_fork(Nat.add(lo, h), Tr.KOne{b}, Tr.KOne{a}, {==}, {==})
        case False{} False{}:
          +g = Tr.KMap.half(rest)
          +n = Nat.add(lo, h)
          +X = Tr.KMap.two(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)))
          tc.mpok_fork(n, Tr.KNil{}, X, {==}, tc.two_mpok(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g))))

def tc.put_mpok(m: Tr.KMap, +hs: List<&2, Nat>, +lo: Nat, +e: Tr.Ent, b: Bool, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.mpok(Tr.KMap.put(m, hs, lo, e, b)) == True{} : Bool}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+f} True{}:
      {==}
    case Tr.KOne{+f} False{}:
      tc.two_mpok(hs, lo, f, e, Nat.is_lt(Tr.Ent.k(f), Nat.add(lo, Tr.KMap.half(hs))), Nat.is_lt(Tr.Ent.k(e), Nat.add(lo, Tr.KMap.half(hs))))
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +P = Tr.KMap.put(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)))
      tc.mpok_fork(mid, P, r, tc.put_mpok(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)), tc.mpok_l(mid, mp, l, r, mk)), tc.mpok_r(mid, mp, l, r, mk))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +P = Tr.KMap.put(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)))
      tc.mpok_fork(mid, l, P, tc.mpok_l(mid, mp, l, r, mk), tc.put_mpok(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)), tc.mpok_r(mid, mp, l, r, mk)))

def tc.unset_mpok(m: Tr.KMap, +x: Nat, b: Bool, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.mpok(Tr.KMap.unset(m, x, b)) == True{} : Bool}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+e} True{}:
      {==}
    case Tr.KOne{+e} False{}:
      {==}
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +U = Tr.KMap.unset(l, x, Tr.KMap.at(l, x))
      tc.mpok_fork(mid, U, r, tc.unset_mpok(l, x, Tr.KMap.at(l, x), tc.mpok_l(mid, mp, l, r, mk)), tc.mpok_r(mid, mp, l, r, mk))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +U = Tr.KMap.unset(r, x, Tr.KMap.at(r, x))
      tc.mpok_fork(mid, l, U, tc.mpok_l(mid, mp, l, r, mk), tc.unset_mpok(r, x, Tr.KMap.at(r, x), tc.mpok_r(mid, mp, l, r, mk)))

def tc.set_mpok(+m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.mpok(Tr.KMap.set(m, hs, e)) == True{} : Bool}:
  tc.put_mpok(m, hs, 0n, e, Tr.KMap.at(m, Tr.Ent.k(e)), mk)

def tc.del_mpok(+m: Tr.KMap, +x: Nat, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.mpok(Tr.KMap.del(m, x)) == True{} : Bool}:
  tc.unset_mpok(m, x, Tr.KMap.at(m, x), mk)

def tc.drop_mpok(ks: List<&2, Nat>, +m: Tr.KMap, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.mpok(Tr.KMap.drop(ks, m)) == True{} : Bool}:
  match ks:
    case Nil{}:
      mk
    case +k <> rest:
      tc.drop_mpok(rest, Tr.KMap.del(m, k), tc.del_mpok(m, k, mk))

# every parent key of t is at most b
def tc.ple(t: List<&2, Tr.Ent>, +b: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(r, b))

def tc.ple_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +pa: {tc.ple(A, b) == True{} : Bool}, +pb: {tc.ple(B, b) == True{} : Bool}) -> {tc.ple(List.append(&2, Tr.Ent, A, B), b) == True{} : Bool}:
  match A:
    case Nil{}:
      pb
    case +e <> +r:
      L.tree.pt.and_t(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(List.append(&2, Tr.Ent, r, B), b), L.tree.pt.and_l(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(r, b), pa), tc.ple_app(r, B, b, L.tree.pt.and_r(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(r, b), pa), pb))

def tc.ple_mono(A: List<&2, Tr.Ent>, +b: Nat, +c: Nat, +pa: {tc.ple(A, b) == True{} : Bool}, +cb: {Nat.is_ge(c, b) == True{} : Bool}) -> {tc.ple(A, c) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +e <> +r:
      L.tree.pt.and_t(Nat.is_ge(c, Tr.Ent.p(e)), tc.ple(r, c), tc.ge_trans(c, b, Tr.Ent.p(e), cb, L.tree.pt.and_l(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(r, b), pa)), tc.ple_mono(r, b, c, L.tree.pt.and_r(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(r, b), pa), cb))

# every parent of the map is at most its largest parent key
def tc.mp_ple(m: Tr.KMap, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.ple(Tr.KMap.read(m), Tr.KMap.mp(m)) == True{} : Bool}:
  match m:
    case Tr.KNil{}:
      {==}
    case Tr.KOne{+e}:
      L.tree.pt.and_t(Nat.is_ge(Tr.Ent.p(e), Tr.Ent.p(e)), True{}, Nat.ge_refl(Tr.Ent.p(e)), {==})
    case Tr.KFork{+mid, +mp, +l, +r}:
      +pl = tc.ple_mono(Tr.KMap.read(l), Tr.KMap.mp(l), mp, tc.mp_ple(l, tc.mpok_l(mid, mp, l, r, mk)), tc.mpok_gl(mid, mp, l, r, mk))
      +pr = tc.ple_mono(Tr.KMap.read(r), Tr.KMap.mp(r), mp, tc.mp_ple(r, tc.mpok_r(mid, mp, l, r, mk)), tc.mpok_gr(mid, mp, l, r, mk))
      tc.ple_app(Tr.KMap.read(l), Tr.KMap.read(r), mp, pl, pr)

# The nodes a delete of x may remove: its node, and the nodes with a
# parent of x or more

def tc.fx.at(c: Bool, +e: Tr.Ent, rest: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match c:
    case True{}:
      e <> rest
    case False{}:
      rest

def tc.fx(t: List<&2, Tr.Ent>, +x: Nat) -> List<&2, Tr.Ent>:
  match t:
    case Nil{}:
      Nil{}
    case +e <> r:
      tc.fx.at(Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), e, tc.fx(r, x))

def tc.fx_at_app(c: Bool, +e: Tr.Ent, +X: List<&2, Tr.Ent>, +Y: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, tc.fx.at(c, e, X), Y) == tc.fx.at(c, e, List.append(&2, Tr.Ent, X, Y)) : List<&2, Tr.Ent>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.fx_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +x: Nat) -> {tc.fx(List.append(&2, Tr.Ent, A, B), x) == List.append(&2, Tr.Ent, tc.fx(A, x), tc.fx(B, x)) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +e <> +r:
      +c = Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x)))
      +ih = tc.fx_app(r, B, x)
      %Equal.sym(List<&2, Tr.Ent>, tc.fx(List.append(&2, Tr.Ent, r, B), x), List.append(&2, Tr.Ent, tc.fx(r, x), tc.fx(B, x)), ih) : {tc.fx.at(c, e, _) == List.append(&2, Tr.Ent, tc.fx.at(c, e, tc.fx(r, x)), tc.fx(B, x)) : List<&2, Tr.Ent>}
      Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, tc.fx.at(c, e, tc.fx(r, x)), tc.fx(B, x)), tc.fx.at(c, e, List.append(&2, Tr.Ent, tc.fx(r, x), tc.fx(B, x))), tc.fx_at_app(c, e, tc.fx(r, x), tc.fx(B, x)))

# no key of t is x
def tc.nokey(t: List<&2, Tr.Ent>, +x: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), tc.nokey(r, x))

def tc.nokey_ge(t: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {L.tc.ge(t, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {tc.nokey(t, x) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      L.tree.pt.and_t(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), tc.nokey(r, x), L.pt.not_t(Nat.is_eq(Tr.Ent.k(e), x), L.tc.ge_miss(e, b, x, L.tc.ge_head(e, r, b, gb), xb)), tc.nokey_ge(r, b, x, L.tc.ge_tail(e, r, b, gb), xb))

def tc.nokey_lt(t: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +lb: {L.tc.lt(t, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {tc.nokey(t, x) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      L.tree.pt.and_t(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), tc.nokey(r, x), L.pt.not_t(Nat.is_eq(Tr.Ent.k(e), x), L.tc.lt_miss(e, b, x, L.tc.lt_head(e, r, b, lb), xb)), tc.nokey_lt(r, b, x, L.tc.lt_tail(e, r, b, lb), xb))

def tc.fx_drop(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, +ne: {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}, +px: {Nat.is_lt(Tr.Ent.p(e), x) == True{} : Bool}) -> {tc.fx(e <> r, x) == tc.fx(r, x) : List<&2, Tr.Ent>}:
  %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ne) : {tc.fx.at(Bool.or(_, Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), e, tc.fx(r, x)) == tc.fx(r, x) : List<&2, Tr.Ent>}
  %Equal.sym(Bool, Nat.is_lt(Tr.Ent.p(e), x), True{}, px) : {tc.fx.at(Bool.or(False{}, Bool.not(_)), e, tc.fx(r, x)) == tc.fx(r, x) : List<&2, Tr.Ent>}
  {==}

# a list with no key x and every parent at most b below x has no node a
# delete of x may remove
def tc.fx_nil(t: List<&2, Tr.Ent>, +x: Nat, +b: Nat, +nk: {tc.nokey(t, x) == True{} : Bool}, +pb: {tc.ple(t, b) == True{} : Bool}, +bx: {Nat.is_lt(b, x) == True{} : Bool}) -> {tc.fx(t, x) == Nil{} : List<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      +ne = L.pt.not_f(Nat.is_eq(Tr.Ent.k(e), x), L.tree.pt.and_l(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), tc.nokey(r, x), nk))
      +px = tc.ge_lt(b, Tr.Ent.p(e), x, L.tree.pt.and_l(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(r, b), pb), bx)
      Equal.trans(List<&2, Tr.Ent>, tc.fx(e <> r, x), tc.fx(r, x), Nil{}, tc.fx_drop(e, r, x, ne, px), tc.fx_nil(r, x, b, L.tree.pt.and_r(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), tc.nokey(r, x), nk), L.tree.pt.and_r(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(r, b), pb), bx))

def tc.not_ff(b: Bool, h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      L.pt.absurd({False{} == True{} : Bool}, h)

def tc.or_fl(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  pt.or_l(a, b, h)

def tc.ups_read(m: Tr.KMap, +x: Nat, +acc: List<&2, Tr.Ent>, gl: Bool, gr: Bool, +egl: {Tr.KMap.gl(m, x) == gl : Bool}, +egr: {Tr.KMap.gr(m, x) == gr : Bool}, +bt: {L.tc.bst(m) == True{} : Bool}, +mk: {tc.mpok(m) == True{} : Bool}) -> {Tr.KMap.ups(m, x, acc, gl, gr) == List.append(&2, Tr.Ent, tc.fx(Tr.KMap.read(m), x), acc) : List<&2, Tr.Ent>}:
  match m gl gr:
    case Tr.KNil{} True{} True{}:
      {==}
    case Tr.KNil{} True{} False{}:
      {==}
    case Tr.KNil{} False{} True{}:
      {==}
    case Tr.KNil{} False{} False{}:
      {==}
    case Tr.KOne{+e} True{} True{}:
      %Equal.sym(Bool, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), True{}, egl) : {e <> acc == List.append(&2, Tr.Ent, tc.fx.at(_, e, Nil{}), acc) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+e} True{} False{}:
      %Equal.sym(Bool, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), True{}, egl) : {e <> acc == List.append(&2, Tr.Ent, tc.fx.at(_, e, Nil{}), acc) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+e} False{} True{}:
      %Equal.sym(Bool, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), False{}, egl) : {acc == List.append(&2, Tr.Ent, tc.fx.at(_, e, Nil{}), acc) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+e} False{} False{}:
      %Equal.sym(Bool, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), False{}, egl) : {acc == List.append(&2, Tr.Ent, tc.fx.at(_, e, Nil{}), acc) : List<&2, Tr.Ent>}
      {==}
    case Tr.KFork{+mid, +mp, +l, +r} True{} True{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +ir = tc.ups_read(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x), {==}, {==}, L.tc.bst_r(mid, mp, l, r, bt), tc.mpok_r(mid, mp, l, r, mk))
      +il = tc.ups_read(l, x, List.append(&2, Tr.Ent, tc.fx(R, x), acc), Tr.KMap.gl(l, x), Tr.KMap.gr(l, x), {==}, {==}, L.tc.bst_l(mid, mp, l, r, bt), tc.mpok_l(mid, mp, l, r, mk))
      %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.ups(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x)), List.append(&2, Tr.Ent, tc.fx(R, x), acc), ir) : {Tr.KMap.ups(l, x, _, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, tc.fx(List.append(&2, Tr.Ent, L, R), x), acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, tc.fx(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, tc.fx(L, x), tc.fx(R, x)), tc.fx_app(L, R, x)) : {Tr.KMap.ups(l, x, List.append(&2, Tr.Ent, tc.fx(R, x), acc), Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, _, acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, tc.fx(L, x), tc.fx(R, x)), acc), List.append(&2, Tr.Ent, tc.fx(L, x), List.append(&2, Tr.Ent, tc.fx(R, x), acc)), tc.app_assoc(tc.fx(L, x), tc.fx(R, x), acc)) : {Tr.KMap.ups(l, x, List.append(&2, Tr.Ent, tc.fx(R, x), acc), Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == _ : List<&2, Tr.Ent>}
      il
    case Tr.KFork{+mid, +mp, +l, +r} True{} False{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +xm = tc.not_ff(Nat.is_lt(x, mid), tc.or_fl(Bool.not(Nat.is_lt(x, mid)), Bool.not(Nat.is_lt(Tr.KMap.mp(r), x)), egr))
      +rx = tc.not_ff(Nat.is_lt(Tr.KMap.mp(r), x), pt.or_r(Bool.not(Nat.is_lt(x, mid)), Bool.not(Nat.is_lt(Tr.KMap.mp(r), x)), egr))
      +nr = tc.fx_nil(R, x, Tr.KMap.mp(r), tc.nokey_ge(R, mid, x, L.tc.bst_ge(mid, mp, l, r, bt), xm), tc.mp_ple(r, tc.mpok_r(mid, mp, l, r, mk)), rx)
      +il = tc.ups_read(l, x, acc, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x), {==}, {==}, L.tc.bst_l(mid, mp, l, r, bt), tc.mpok_l(mid, mp, l, r, mk))
      %Equal.sym(List<&2, Tr.Ent>, tc.fx(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, tc.fx(L, x), tc.fx(R, x)), tc.fx_app(L, R, x)) : {Tr.KMap.ups(l, x, acc, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, _, acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, tc.fx(R, x), Nil{}, nr) : {Tr.KMap.ups(l, x, acc, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, tc.fx(L, x), _), acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, tc.fx(L, x), Nil{}), tc.fx(L, x), L.tc.app_nil(tc.fx(L, x))) : {Tr.KMap.ups(l, x, acc, Tr.KMap.gl(l, x), Tr.KMap.gr(l, x)) == List.append(&2, Tr.Ent, _, acc) : List<&2, Tr.Ent>}
      il
    case Tr.KFork{+mid, +mp, +l, +r} False{} True{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +xm = pt.or_l(Nat.is_lt(x, mid), Bool.not(Nat.is_lt(Tr.KMap.mp(l), x)), egl)
      +lx = tc.not_ff(Nat.is_lt(Tr.KMap.mp(l), x), pt.or_r(Nat.is_lt(x, mid), Bool.not(Nat.is_lt(Tr.KMap.mp(l), x)), egl))
      +nl = tc.fx_nil(L, x, Tr.KMap.mp(l), tc.nokey_lt(L, mid, x, L.tc.bst_lt(mid, mp, l, r, bt), xm), tc.mp_ple(l, tc.mpok_l(mid, mp, l, r, mk)), lx)
      +ir = tc.ups_read(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x), {==}, {==}, L.tc.bst_r(mid, mp, l, r, bt), tc.mpok_r(mid, mp, l, r, mk))
      %Equal.sym(List<&2, Tr.Ent>, tc.fx(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, tc.fx(L, x), tc.fx(R, x)), tc.fx_app(L, R, x)) : {Tr.KMap.ups(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x)) == List.append(&2, Tr.Ent, _, acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, tc.fx(L, x), Nil{}, nl) : {Tr.KMap.ups(r, x, acc, Tr.KMap.gl(r, x), Tr.KMap.gr(r, x)) == List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, _, tc.fx(R, x)), acc) : List<&2, Tr.Ent>}
      ir
    case Tr.KFork{+mid, +mp, +l, +r} False{} False{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +xm = pt.or_l(Nat.is_lt(x, mid), Bool.not(Nat.is_lt(Tr.KMap.mp(l), x)), egl)
      +lx = tc.not_ff(Nat.is_lt(Tr.KMap.mp(l), x), pt.or_r(Nat.is_lt(x, mid), Bool.not(Nat.is_lt(Tr.KMap.mp(l), x)), egl))
      +rx = tc.not_ff(Nat.is_lt(Tr.KMap.mp(r), x), pt.or_r(Bool.not(Nat.is_lt(x, mid)), Bool.not(Nat.is_lt(Tr.KMap.mp(r), x)), egr))
      +xm2 = tc.not_ff(Nat.is_lt(x, mid), tc.or_fl(Bool.not(Nat.is_lt(x, mid)), Bool.not(Nat.is_lt(Tr.KMap.mp(r), x)), egr))
      L.pt.absurd({acc == List.append(&2, Tr.Ent, tc.fx(List.append(&2, Tr.Ent, L, R), x), acc) : List<&2, Tr.Ent>}, Equal.trans(Bool, True{}, Nat.is_lt(x, mid), False{}, Equal.sym(Bool, Nat.is_lt(x, mid), True{}, xm2), xm))

# every key of gone is x, or below every key of s
def tc.gb(gone: List<&2, Nat>, +x: Nat, +s: List<&2, Tr.Ent>) -> Bool:
  match gone:
    case Nil{}:
      True{}
    case +z <> rest:
      Bool.and(Bool.or(Nat.is_eq(z, x), Tr.above(z, s)), tc.gb(rest, x, s))

def tc.gb_tail(gone: List<&2, Nat>, +x: Nat, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +g: {tc.gb(gone, x, e <> r) == True{} : Bool}, +st: {Tr.sorted(e <> r) == True{} : Bool}) -> {tc.gb(gone, x, r) == True{} : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +z <> +rest:
      +hd = L.tree.pt.and_l(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), tc.gb(rest, x, e <> r), g)
      +tl = L.tree.pt.and_r(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), tc.gb(rest, x, e <> r), g)
      L.tree.pt.and_t(Bool.or(Nat.is_eq(z, x), Tr.above(z, r)), tc.gb(rest, x, r), pt.or_above_tail(Nat.is_eq(z, x), z, e, r, hd, st), tc.gb_tail(rest, x, e, r, tl, st))

def tc.gb_hd(c: Bool, +z: Nat, +x: Nat, +k: Nat, +ec: {Nat.is_eq(z, x) == c : Bool}, +h: {Bool.or(c, Nat.is_lt(z, k)) == True{} : Bool}, +kx: {Nat.is_eq(k, x) == False{} : Bool}) -> {Nat.is_eq(z, k) == False{} : Bool}:
  match c:
    case True{}:
      +zx = pt.eq_true(z, x, ec)
      %Equal.sym(Nat, z, x, zx) : {Nat.is_eq(_, k) == False{} : Bool}
      L.pt.ne_comm(k, x, kx)
    case False{}:
      L.pt.lt_ne(z, k, h)

# a key that is not x is not gone, while gone holds x and keys below it
def tc.gb_elem(gone: List<&2, Nat>, +x: Nat, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +g: {tc.gb(gone, x, e <> r) == True{} : Bool}, +kx: {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}) -> {Tr.elem(gone, Tr.Ent.k(e)) == False{} : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +z <> +rest:
      +hd = L.tree.pt.and_l(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), tc.gb(rest, x, e <> r), g)
      +tl = L.tree.pt.and_r(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), tc.gb(rest, x, e <> r), g)
      +ne = tc.gb_hd(Nat.is_eq(z, x), z, x, Tr.Ent.k(e), {==}, hd, kx)
      %Equal.sym(Bool, Nat.is_eq(z, Tr.Ent.k(e)), False{}, ne) : {Bool.or(_, Tr.elem(rest, Tr.Ent.k(e))) == False{} : Bool}
      tc.gb_elem(rest, x, e, r, tl, kx)

def tc.nlt_go(+a: Nat, +b: Nat, +c: Nat, d: Bool, +ed: {Nat.is_lt(c, b) == d : Bool}, +ac: {Nat.is_lt(a, c) == True{} : Bool}, +nab: {Nat.is_lt(a, b) == False{} : Bool}) -> {d == False{} : Bool}:
  match d:
    case True{}:
      L.pt.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, Nat.is_lt(a, b), False{}, Equal.sym(Bool, Nat.is_lt(a, b), True{}, pt.lt_trans(a, c, b, ac, ed)), nab))
    case False{}:
      {==}

# a below c and a not below b: c not below b
def tc.nlt_up(+a: Nat, +b: Nat, +c: Nat, +ac: {Nat.is_lt(a, c) == True{} : Bool}, +nab: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_lt(c, b) == False{} : Bool}:
  tc.nlt_go(a, b, c, Nat.is_lt(c, b), {==}, ac, nab)

# a kept node's key is x or more
def tc.kept_ge(+e: Tr.Ent, +x: Nat, c: Bool, +ec: {Nat.is_eq(Tr.Ent.k(e), x) == c : Bool}, +h: {Bool.or(c, Bool.not(Nat.is_lt(Tr.Ent.p(e), x))) == True{} : Bool}, +pk: {Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)) == True{} : Bool}) -> {Nat.is_lt(Tr.Ent.k(e), x) == False{} : Bool}:
  match c:
    case True{}:
      +kx = pt.eq_true(Tr.Ent.k(e), x, ec)
      %kx : {Nat.is_lt(Tr.Ent.k(e), _) == False{} : Bool}
      L.pt.lt_irrefl(Tr.Ent.k(e))
    case False{}:
      +px = L.pt.not_f(Nat.is_lt(Tr.Ent.p(e), x), h)
      tc.nlt_up(Tr.Ent.p(e), x, Tr.Ent.k(e), pk, px)

def tc.fd_at(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +eh: {Tr.gone.at(e <> r, gone) == hit : Bool}, +x: Nat, c: Bool, +ec: {Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))) == c : Bool}, +ng: {tc.nall(gone, x) == True{} : Bool}, +g: {tc.gb(gone, x, e <> r) == True{} : Bool}, +pk: {Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)) == True{} : Bool}, +ih1: {tc.dgo(r, gone, Tr.gone.at(r, gone)) == tc.dgo(tc.fx(r, x), gone, Tr.gone.at(tc.fx(r, x), gone)) : List<&2, Nat>}, ih2: {Nat.is_lt(Tr.Ent.k(e), x) == False{} : Bool} -> {tc.dgo(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone)) == tc.dgo(tc.fx(r, x), Tr.Ent.k(e) <> gone, Tr.gone.at(tc.fx(r, x), Tr.Ent.k(e) <> gone)) : List<&2, Nat>}) -> {tc.dgo(e <> r, gone, hit) == tc.dgo(tc.fx.at(c, e, tc.fx(r, x)), gone, Tr.gone.at(tc.fx.at(c, e, tc.fx(r, x)), gone)) : List<&2, Nat>}:
  match c:
    case True{}:
      +G = Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e)))
      +kx = tc.kept_ge(e, x, Nat.is_eq(Tr.Ent.k(e), x), {==}, ec, pk)
      %Equal.sym(Bool, G, hit, eh) : {tc.dgo(e <> r, gone, hit) == tc.dgo(e <> tc.fx(r, x), gone, _) : List<&2, Nat>}
      tc.dg_ge(hit, e, r, tc.fx(r, x), gone, ih1, ih2(kx))
    case False{}:
      +ne = pt.or_l(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x)), ec)
      +px = tc.not_ff(Nat.is_lt(Tr.Ent.p(e), x), pt.or_r(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x)), ec))
      +nk = tc.gb_elem(gone, x, e, r, g, ne)
      +np = tc.elem_none(gone, x, Tr.Ent.p(e), ng, px)
      +o = tc.or_ff(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e)), nk, np)
      +hf = Equal.trans(Bool, hit, Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))), False{}, Equal.sym(Bool, Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))), hit, eh), o)
      %Equal.sym(Bool, hit, False{}, hf) : {tc.dgo(e <> r, gone, _) == tc.dgo(tc.fx(r, x), gone, Tr.gone.at(tc.fx(r, x), gone)) : List<&2, Nat>}
      ih1

# a delete's walk over the nodes it may remove drops the keys of the walk
# over every node
def tc.drops_fx(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +eh: {Tr.gone.at(s, gone) == hit : Bool}, +x: Nat, +ng: {tc.nall(gone, x) == True{} : Bool}, +g: {tc.gb(gone, x, s) == True{} : Bool}, +st: {Tr.sorted(s) == True{} : Bool}, +dk: {tc.desc(s) == True{} : Bool}) -> {tc.dgo(s, gone, hit) == tc.dgo(tc.fx(s, x), gone, Tr.gone.at(tc.fx(s, x), gone)) : List<&2, Nat>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +pk = L.tree.pt.and_l(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), tc.desc(r), dk)
      +dr = L.tree.pt.and_r(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), tc.desc(r), dk)
      +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
      +ar = L.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
      +g1 = tc.gb_tail(gone, x, e, r, g, st)
      +g2 = L.tree.pt.and_t(Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Tr.above(Tr.Ent.k(e), r)), tc.gb(gone, x, r), pt.or_tr(Nat.is_eq(Tr.Ent.k(e), x), Tr.above(Tr.Ent.k(e), r), ar), g1)
      +ih1 = tc.drops_fx(r, gone, Tr.gone.at(r, gone), {==}, x, ng, g1, sr, dr)
      tc.fd_at(e, r, gone, hit, eh, x, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), {==}, ng, g, pk, ih1, kx => tc.drops_fx(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone), {==}, x, tc.nall_cons(Tr.Ent.k(e), gone, x, kx, ng), g2, sr, dr))

# every key of ks is above k
def tc.gtall(ks: List<&2, Nat>, +k: Nat) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case +z <> rest:
      Bool.and(Nat.is_lt(k, z), tc.gtall(rest, k))

def tc.drops_gt(r: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +k: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}) -> {tc.gtall(tc.dgo(r, gone, hit), k) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +f <> +r2:
      match hit:
        case True{}:
          +af = L.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +sr2 = L.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +ar2 = pt.above_lt(k, Tr.Ent.k(f), r2, ar, af)
          +g2 = {Tr.Ent.k(f) <> gone : List<&2, Nat>}
          L.tree.pt.and_t(Nat.is_lt(k, Tr.Ent.k(f)), tc.gtall(tc.dgo(r2, g2, Tr.gone.at(r2, g2)), k), ar, tc.drops_gt(r2, g2, Tr.gone.at(r2, g2), k, ar2, sr2))
        case False{}:
          +af = L.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +sr2 = L.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
          +ar2 = pt.above_lt(k, Tr.Ent.k(f), r2, ar, af)
          tc.drops_gt(r2, gone, Tr.gone.at(r2, gone), k, ar2, sr2)

# an unset of a key above the head keeps the head
def tc.unsets_cons(ks: List<&2, Nat>, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +gt: {tc.gtall(ks, Tr.Ent.k(e)) == True{} : Bool}) -> {tc.unsets(ks, e <> r) == e <> tc.unsets(ks, r) : List<&2, Tr.Ent>}:
  match ks:
    case Nil{}:
      {==}
    case +z <> +rest:
      +lt = L.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), z), tc.gtall(rest, Tr.Ent.k(e)), gt)
      +ne = L.pt.lt_ne(Tr.Ent.k(e), z, lt)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), z), False{}, ne) : {tc.unsets(rest, Tr.unset.go(e <> r, z, _)) == e <> tc.unsets(rest, Tr.unset(r, z)) : List<&2, Tr.Ent>}
      tc.unsets_cons(rest, e, Tr.unset(r, z), L.tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), z), tc.gtall(rest, Tr.Ent.k(e)), gt))

# an unset of a key below every key of r keeps r
def tc.unset_above(r: List<&2, Tr.Ent>, +k: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}) -> {Tr.unset(r, k) == r : List<&2, Tr.Ent>}:
  match r:
    case Nil{}:
      {==}
    case +f <> +r2:
      +ne = L.pt.lt_ne_r(k, Tr.Ent.k(f), ar)
      +af = L.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
      +sr2 = L.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(f), k), False{}, ne) : {Tr.unset.go(f <> r2, k, _) == f <> r2 : List<&2, Tr.Ent>}
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => f <> ys, Tr.unset(r2, k), r2, tc.unset_above(r2, k, pt.above_lt(k, Tr.Ent.k(f), r2, ar, af), sr2))

# unsetting the keys a walk drops is the walk's prune
def tc.unsets_drops(t: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {tc.unsets(tc.dgo(t, gone, hit), t) == Tr.prune.go(t, gone, hit) : List<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ar = L.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +g2 = {Tr.Ent.k(e) <> gone : List<&2, Nat>}
          +D = tc.dgo(r, g2, Tr.gone.at(r, g2))
          %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), Tr.Ent.k(e)), True{}, Equal.sym(Bool, True{}, Nat.is_eq(Tr.Ent.k(e), Tr.Ent.k(e)), pt.eq_refl(Tr.Ent.k(e)))) : {tc.unsets(D, Tr.unset.go(e <> r, Tr.Ent.k(e), _)) == Tr.prune.go(r, g2, Tr.gone.at(r, g2)) : List<&2, Tr.Ent>}
          %Equal.sym(List<&2, Tr.Ent>, Tr.unset(r, Tr.Ent.k(e)), r, tc.unset_above(r, Tr.Ent.k(e), ar, sr)) : {tc.unsets(D, _) == Tr.prune.go(r, g2, Tr.gone.at(r, g2)) : List<&2, Tr.Ent>}
          tc.unsets_drops(r, g2, Tr.gone.at(r, g2), sr)
        case False{}:
          +ar = L.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +D = tc.dgo(r, gone, Tr.gone.at(r, gone))
          +gt = tc.drops_gt(r, gone, Tr.gone.at(r, gone), Tr.Ent.k(e), ar, sr)
          Equal.trans(List<&2, Tr.Ent>, tc.unsets(D, e <> r), e <> tc.unsets(D, r), e <> Tr.prune.go(r, gone, Tr.gone.at(r, gone)), tc.unsets_cons(D, e, r, gt), Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => e <> ys, tc.unsets(D, r), Tr.prune.go(r, gone, Tr.gone.at(r, gone)), tc.unsets_drops(r, gone, Tr.gone.at(r, gone), sr)))

# A record on the map

def tc.onto(m: Tr.KMap, +acc: List<&2, Tr.Ent>) -> {Tr.KMap.onto(m, acc) == List.append(&2, Tr.Ent, Tr.KMap.read(m), acc) : List<&2, Tr.Ent>}:
  match m:
    case Tr.KNil{}:
      {==}
    case Tr.KOne{e}:
      {==}
    case Tr.KFork{mid, mp, +l, +r}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.onto(r, acc), List.append(&2, Tr.Ent, R, acc), tc.onto(r, acc)) : {Tr.KMap.onto(l, _) == List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, L, R), acc) : List<&2, Tr.Ent>}
      %Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, L, R), acc), List.append(&2, Tr.Ent, L, List.append(&2, Tr.Ent, R, acc)), tc.app_assoc(L, R, acc)) : {Tr.KMap.onto(l, List.append(&2, Tr.Ent, R, acc)) == _ : List<&2, Tr.Ent>}
      tc.onto(l, List.append(&2, Tr.Ent, R, acc))

def tc.onto_nil(+m: Tr.KMap) -> {Tr.KMap.onto(m, Nil{}) == Tr.KMap.read(m) : List<&2, Tr.Ent>}:
  Equal.trans(List<&2, Tr.Ent>, Tr.KMap.onto(m, Nil{}), List.append(&2, Tr.Ent, Tr.KMap.read(m), Nil{}), Tr.KMap.read(m), tc.onto(m, Nil{}), L.tc.app_nil(Tr.KMap.read(m)))

def tc.hangs(s: List<&2, Tr.Ent>, +m: Tr.KMap, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.hangs(s, m) == Tr.rooted.go(s, Tr.KMap.read(m)) : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +p = Tr.Ent.p(e)
      %Equal.sym(Bool, Tr.KMap.has(m, p), Tr.has(Tr.KMap.read(m), p), tc.has(m, p, bt)) : {Bool.and(Bool.and(Nat.is_lt(p, Tr.Ent.k(e)), Bool.or(Nat.is_eq(p, 0n), _)), Tr.KMap.hangs(rest, m)) == Tr.rooted.go(e <> rest, Tr.KMap.read(m)) : Bool}
      %Equal.sym(Bool, Tr.KMap.hangs(rest, m), Tr.rooted.go(rest, Tr.KMap.read(m)), tc.hangs(rest, m, bt)) : {Bool.and(Bool.and(Nat.is_lt(p, Tr.Ent.k(e)), Bool.or(Nat.is_eq(p, 0n), Tr.has(Tr.KMap.read(m), p))), _) == Tr.rooted.go(e <> rest, Tr.KMap.read(m)) : Bool}
      {==}

def tc.exact_read(+m: Tr.KMap, +hs: List<&2, Nat>, o: Tr.Op, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.exact(m, hs, o)) == Tr.exact(Tr.KMap.read(m), o) : List<&2, Tr.Ent>}:
  match o:
    case Tr.Put{+k, +p, +v}:
      tc.set_read(m, hs, Tr.Ent{k, p, v}, bt)
    case Tr.Del{+x}:
      tc.del_read(m, x, bt)

def tc.patch_read(ops: List<&2, Tr.Op>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.patch(ops, hs, m)) == Tr.patch(ops, Tr.KMap.read(m)) : List<&2, Tr.Ent>}:
  match ops:
    case Nil{}:
      {==}
    case +o <> rest:
      +E = Tr.KMap.exact(m, hs, o)
      %tc.exact_read(m, hs, o, bt) : {Tr.KMap.read(Tr.KMap.patch(rest, hs, E)) == Tr.patch(rest, _) : List<&2, Tr.Ent>}
      tc.patch_read(rest, hs, E, L.tc.exact_bst(m, hs, o, bt))

# the test of a put on the map is ok on the list
def tc.good_put(+m: Tr.KMap, +k: Nat, +p: Nat, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.KMap.has(m, p))) == Tr.ok(Tr.KMap.read(m), k, p) : Bool}:
  %Equal.sym(Bool, Tr.KMap.has(m, p), Tr.has(Tr.KMap.read(m), p), tc.has(m, p, bt)) : {Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), _)) == Tr.ok(Tr.KMap.read(m), k, p) : Bool}
  {==}

# the test of a rewind on the map is sound on the list
def tc.good_rewind(+ops: List<&2, Tr.Op>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.hangs(Tr.KMap.onto(Tr.KMap.patch(ops, hs, m), Nil{}), Tr.KMap.patch(ops, hs, m)) == Tr.sound(Tr.patch(ops, Tr.KMap.read(m))) : Bool}:
  +n = Tr.KMap.patch(ops, hs, m)
  +bn = L.tc.patch_bst(ops, hs, m, bt)
  +N = Tr.KMap.read(n)
  %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.onto(n, Nil{}), N, tc.onto_nil(n)) : {Tr.KMap.hangs(_, n) == Tr.sound(Tr.patch(ops, Tr.KMap.read(m))) : Bool}
  %Equal.sym(Bool, Tr.KMap.hangs(N, n), Tr.rooted.go(N, N), tc.hangs(N, n, bn)) : {_ == Tr.sound(Tr.patch(ops, Tr.KMap.read(m))) : Bool}
  %tc.patch_read(ops, hs, m, bt) : {Tr.rooted.go(N, N) == Tr.sound(_) : Bool}
  %Equal.sym(Bool, Tr.sorted(N), True{}, tc.sorted_read(n, bn)) : {Tr.rooted.go(N, N) == Bool.and(_, Tr.rooted(N)) : Bool}
  {==}

def tc.put_case(b: Bool, +m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +bt: {L.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.put.ans(b, m, hs, e))) == Tr.put.at(b, Tr.KMap.read(m), e) : List<&2, Tr.Ent>}:
  match b:
    case True{}:
      tc.set_read(m, hs, e, bt)
    case False{}:
      {==}

def tc.keep_case(b: Bool, +m: Tr.KMap, +n: Tr.KMap, +N: List<&2, Tr.Ent>, +rn: {Tr.KMap.read(n) == N : List<&2, Tr.Ent>}) -> {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.keep.ans(b, m, n))) == Tr.keep.at(b, Tr.KMap.read(m), N) : List<&2, Tr.Ent>}:
  match b:
    case True{}:
      rn
    case False{}:
      {==}

def tc.keep_case_bst2(b: Bool, +m: Tr.KMap, +n: Tr.KMap, +bm: {tc.mpok(m) == True{} : Bool}, +bn: {tc.mpok(n) == True{} : Bool}) -> {tc.mpok(Pair.fst(Tr.KMap, Tr.Ans, Tr.keep.ans(b, m, n))) == True{} : Bool}:
  match b:
    case True{}:
      bn
    case False{}:
      bm

# The gone map
# the gone keys of a list, as the gone map holds them
def tc.bld(gone: List<&2, Nat>) -> List<&2, Tr.Ent>:
  match gone:
    case Nil{}:
      Nil{}
    case k <> rest:
      Tr.set(tc.bld(rest), Tr.Ent{k, 0n, 0n})

def tc.has_set.go(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +y: Nat, b: Bool, eb: {Nat.is_eq(Tr.Ent.k(e), y) == b : Bool}) -> {Tr.has(Tr.set(t, e), y) == Bool.or(b, Tr.has(t, y)) : Bool}:
  match b:
    case True{}:
      %pt.eq_true(Tr.Ent.k(e), y, eb) : {Tr.has(Tr.set(t, e), _) == True{} : Bool}
      Equal.cong(Maybe<&2, Tr.Ent>, Bool, z => Maybe.is_some(&2, Tr.Ent, z), Tr.get(Tr.set(t, e), Tr.Ent.k(e)), Some{e}, pt.get_set_same(t, e))
    case False{}:
      Equal.cong(Maybe<&2, Tr.Ent>, Bool, z => Maybe.is_some(&2, Tr.Ent, z), Tr.get(Tr.set(t, e), y), Tr.get(t, y), pt.get_set_other(t, e, y, eb))

# a set holds its key and every key it held
def tc.has_set(+t: List<&2, Tr.Ent>, +e: Tr.Ent, +y: Nat) -> {Tr.has(Tr.set(t, e), y) == Bool.or(Nat.is_eq(Tr.Ent.k(e), y), Tr.has(t, y)) : Bool}:
  tc.has_set.go(t, e, y, Nat.is_eq(Tr.Ent.k(e), y), {==})

# the gone keys hold exactly the keys of the gone list
def tc.bld_has(gone: List<&2, Nat>, +y: Nat) -> {Tr.has(tc.bld(gone), y) == Tr.elem(gone, y) : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +k <> +rest:
      Equal.trans(Bool, Tr.has(Tr.set(tc.bld(rest), Tr.Ent{k, 0n, 0n}), y), Bool.or(Nat.is_eq(k, y), Tr.has(tc.bld(rest), y)), Bool.or(Nat.is_eq(k, y), Tr.elem(rest, y)), tc.has_set(tc.bld(rest), Tr.Ent{k, 0n, 0n}, y), Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(k, y), z), Tr.has(tc.bld(rest), y), Tr.elem(rest, y), tc.bld_has(rest, y)))

# the gone map holds what the gone list holds
def tc.ghas(+g: Tr.KMap, +gone: List<&2, Nat>, +y: Nat, +bt: {L.tc.bst(g) == True{} : Bool}, +rg: {Tr.KMap.read(g) == tc.bld(gone) : List<&2, Tr.Ent>}) -> {Tr.KMap.has(g, y) == Tr.elem(gone, y) : Bool}:
  Equal.trans(Bool, Tr.KMap.has(g, y), Tr.has(Tr.KMap.read(g), y), Tr.elem(gone, y), tc.has(g, y, bt), Equal.trans(Bool, Tr.has(Tr.KMap.read(g), y), Tr.has(tc.bld(gone), y), Tr.elem(gone, y), Equal.cong(List<&2, Tr.Ent>, Bool, z => Tr.has(z, y), Tr.KMap.read(g), tc.bld(gone), rg), tc.bld_has(gone, y)))

# the gone test of the map is the gone test of the list
def tc.gin(s: List<&2, Tr.Ent>, +g: Tr.KMap, +gone: List<&2, Nat>, +bt: {L.tc.bst(g) == True{} : Bool}, +rg: {Tr.KMap.read(g) == tc.bld(gone) : List<&2, Tr.Ent>}) -> {Tr.gone.in(s, g) == Tr.gone.at(s, gone) : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> r:
      %Equal.sym(Bool, Tr.KMap.has(g, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.k(e)), tc.ghas(g, gone, Tr.Ent.k(e), bt, rg)) : {Bool.or(_, Tr.KMap.has(g, Tr.Ent.p(e))) == Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))) : Bool}
      %Equal.sym(Bool, Tr.KMap.has(g, Tr.Ent.p(e)), Tr.elem(gone, Tr.Ent.p(e)), tc.ghas(g, gone, Tr.Ent.p(e), bt, rg)) : {Bool.or(Tr.elem(gone, Tr.Ent.k(e)), _) == Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))) : Bool}
      {==}

# a key joins the gone map as it joins the gone list
def tc.gone_of(+hs: List<&2, Nat>, +g: Tr.KMap, +gone: List<&2, Nat>, +k: Nat, +bt: {L.tc.bst(g) == True{} : Bool}, +rg: {Tr.KMap.read(g) == tc.bld(gone) : List<&2, Tr.Ent>}) -> {Tr.KMap.read(Tr.gone.of(hs, g, k)) == tc.bld(k <> gone) : List<&2, Tr.Ent>}:
  Equal.trans(List<&2, Tr.Ent>, Tr.KMap.read(Tr.KMap.set(g, hs, Tr.Ent{k, 0n, 0n})), Tr.set(Tr.KMap.read(g), Tr.Ent{k, 0n, 0n}), tc.bld(k <> gone), tc.set_read(g, hs, Tr.Ent{k, 0n, 0n}, bt), Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, z => Tr.set(z, Tr.Ent{k, 0n, 0n}), Tr.KMap.read(g), tc.bld(gone), rg))

# the walk over the gone map drops what the walk over the gone list drops
def tc.ds(s: List<&2, Tr.Ent>, +hs: List<&2, Nat>, +g: Tr.KMap, +gone: List<&2, Nat>, hit: Bool, +bt: {L.tc.bst(g) == True{} : Bool}, +rg: {Tr.KMap.read(g) == tc.bld(gone) : List<&2, Tr.Ent>}) -> {Tr.drops.s(s, hs, g, hit) == tc.dgo(s, gone, hit) : List<&2, Nat>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +k = Tr.Ent.k(e)
          +g2 = Tr.gone.of(hs, g, k)
          +gn = {k <> gone : List<&2, Nat>}
          +bt2 = L.tc.set_bst(g, hs, Tr.Ent{k, 0n, 0n}, bt)
          +rg2 = tc.gone_of(hs, g, gone, k, bt, rg)
          %Equal.sym(Bool, Tr.gone.in(r, g2), Tr.gone.at(r, gn), tc.gin(r, g2, gn, bt2, rg2)) : {k <> Tr.drops.s(r, hs, g2, _) == k <> tc.dgo(r, gn, Tr.gone.at(r, gn)) : List<&2, Nat>}
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => k <> z, Tr.drops.s(r, hs, g2, Tr.gone.at(r, gn)), tc.dgo(r, gn, Tr.gone.at(r, gn)), tc.ds(r, hs, g2, gn, Tr.gone.at(r, gn), bt2, rg2))
        case False{}:
          %Equal.sym(Bool, Tr.gone.in(r, g), Tr.gone.at(r, gone), tc.gin(r, g, gone, bt, rg)) : {Tr.drops.s(r, hs, g, _) == tc.dgo(r, gone, Tr.gone.at(r, gone)) : List<&2, Nat>}
          tc.ds(r, hs, g, gone, Tr.gone.at(r, gone), bt, rg)

# a delete's walk with the gone map drops what the walk with the gone list
# [x] drops
def tc.drops(+s: List<&2, Tr.Ent>, +hs: List<&2, Nat>, +x: Nat) -> {Tr.drops(s, hs, x) == tc.dgo(s, [x], Tr.gone.at(s, [x])) : List<&2, Nat>}:
  +g = Tr.gone.of(hs, Tr.KNil{}, x)
  +bt = L.tc.set_bst(Tr.KNil{}, hs, Tr.Ent{x, 0n, 0n}, {==})
  +rg = tc.gone_of(hs, Tr.KNil{}, Nil{}, x, {==}, {==})
  %Equal.sym(Bool, Tr.gone.in(s, g), Tr.gone.at(s, [x]), tc.gin(s, g, [x], bt, rg)) : {Tr.drops.s(s, hs, g, _) == tc.dgo(s, [x], Tr.gone.at(s, [x])) : List<&2, Nat>}
  tc.ds(s, hs, g, [x], Tr.gone.at(s, [x]), bt, rg)

# the keys a delete of x cuts on the map are the keys the walk drops
def tc.del_keys(+m: Tr.KMap, +x: Nat, +bt: {L.tc.bst(m) == True{} : Bool}, +mk: {tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {tc.dgo(Tr.KMap.ups(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x)), [x], Tr.gone.at(Tr.KMap.ups(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x)), [x])) == tc.dgo(Tr.KMap.read(m), [x], Tr.gone.at(Tr.KMap.read(m), [x])) : List<&2, Nat>}:
  +t = Tr.KMap.read(m)
  +U = Tr.KMap.ups(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x))
  +rf = Equal.trans(List<&2, Tr.Ent>, U, List.append(&2, Tr.Ent, tc.fx(t, x), Nil{}), tc.fx(t, x), tc.ups_read(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x), {==}, {==}, bt, mk), L.tc.app_nil(tc.fx(t, x)))
  +ng = L.tree.pt.and_t(Bool.not(Nat.is_lt(x, x)), True{}, L.pt.not_t(Nat.is_lt(x, x), L.pt.lt_irrefl(x)), {==})
  +g = L.tree.pt.and_t(Bool.or(Nat.is_eq(x, x), Tr.above(x, t)), True{}, pt.or_tl(Nat.is_eq(x, x), Tr.above(x, t), Equal.sym(Bool, True{}, Nat.is_eq(x, x), pt.eq_refl(x))), {==})
  +dk = tc.desc_of(t, t, L.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), sd))
  %Equal.sym(List<&2, Tr.Ent>, U, tc.fx(t, x), rf) : {tc.dgo(_, [x], Tr.gone.at(_, [x])) == tc.dgo(t, [x], Tr.gone.at(t, [x])) : List<&2, Nat>}
  Equal.sym(List<&2, Nat>, tc.dgo(t, [x], Tr.gone.at(t, [x])), tc.dgo(tc.fx(t, x), [x], Tr.gone.at(tc.fx(t, x), [x])), tc.drops_fx(t, [x], Tr.gone.at(t, [x]), {==}, x, ng, g, tc.sorted_read(m, bt), dk))

def tc.rec_read(+m: Tr.KMap, +hs: List<&2, Nat>, r: Tr.Rec, +bt: {L.tc.bst(m) == True{} : Bool}, +mk: {tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))) == Tr.apply(Tr.KMap.read(m), r) : List<&2, Tr.Ent>}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          +e = {Tr.Ent{k, p, v} : Tr.Ent}
          +G = Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.KMap.has(m, p)))
          %Equal.sym(Bool, G, Tr.ok(Tr.KMap.read(m), k, p), tc.good_put(m, k, p, bt)) : {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.put.ans(_, m, hs, e))) == Tr.put.at(Tr.ok(Tr.KMap.read(m), k, p), Tr.KMap.read(m), e) : List<&2, Tr.Ent>}
          tc.put_case(Tr.ok(Tr.KMap.read(m), k, p), m, hs, e, bt)
        case Tr.Del{x}:
          match x:
            case 0n:
              {==}
            case 1n++y:
              +t = Tr.KMap.read(m)
              +F = Tr.KMap.ups(m, 1n+y, Nil{}, Tr.KMap.gl(m, 1n+y), Tr.KMap.gr(m, 1n+y))
              +KS = Tr.drops(F, hs, 1n+y)
              +K2 = tc.dgo(F, [1n+y], Tr.gone.at(F, [1n+y]))
              +D = tc.dgo(t, [1n+y], Tr.gone.at(t, [1n+y]))
              +s1 = tc.drop_read(KS, m, bt)
              +s2 = Equal.cong(List<&2, Nat>, List<&2, Tr.Ent>, z => tc.unsets(z, t), KS, D, Equal.trans(List<&2, Nat>, KS, K2, D, tc.drops(F, hs, 1n+y), tc.del_keys(m, 1n+y, bt, mk, sd)))
              +s3 = tc.unsets_drops(t, [1n+y], Tr.gone.at(t, [1n+y]), tc.sorted_read(m, bt))
              Equal.trans(List<&2, Tr.Ent>, Tr.KMap.read(Tr.KMap.drop(KS, m)), tc.unsets(KS, t), Tr.prune(t, 1n+y), s1, Equal.trans(List<&2, Tr.Ent>, tc.unsets(KS, t), tc.unsets(D, t), Tr.prune(t, 1n+y), s2, s3))
    case Tr.Rewind{+ops}:
      +n = Tr.KMap.patch(ops, hs, m)
      +G = Tr.KMap.hangs(Tr.KMap.onto(n, Nil{}), n)
      +N = Tr.patch(ops, Tr.KMap.read(m))
      %Equal.sym(Bool, G, Tr.sound(N), tc.good_rewind(ops, hs, m, bt)) : {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.keep.ans(_, m, n))) == Tr.keep.at(Tr.sound(N), Tr.KMap.read(m), N) : List<&2, Tr.Ent>}
      tc.keep_case(Tr.sound(N), m, n, N, tc.patch_read(ops, hs, m, bt))

def tc.exact_mpok(+m: Tr.KMap, +hs: List<&2, Nat>, o: Tr.Op, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.mpok(Tr.KMap.exact(m, hs, o)) == True{} : Bool}:
  match o:
    case Tr.Put{+k, +p, +v}:
      tc.set_mpok(m, hs, Tr.Ent{k, p, v}, mk)
    case Tr.Del{+x}:
      tc.del_mpok(m, x, mk)

def tc.patch_mpok(ops: List<&2, Tr.Op>, +hs: List<&2, Nat>, +m: Tr.KMap, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.mpok(Tr.KMap.patch(ops, hs, m)) == True{} : Bool}:
  match ops:
    case Nil{}:
      mk
    case +o <> rest:
      tc.patch_mpok(rest, hs, Tr.KMap.exact(m, hs, o), tc.exact_mpok(m, hs, o, mk))

def tc.put_case_mpok(b: Bool, +m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.mpok(Pair.fst(Tr.KMap, Tr.Ans, Tr.put.ans(b, m, hs, e))) == True{} : Bool}:
  match b:
    case True{}:
      tc.set_mpok(m, hs, e, mk)
    case False{}:
      mk

def tc.rec_mpok(+m: Tr.KMap, +hs: List<&2, Nat>, r: Tr.Rec, +mk: {tc.mpok(m) == True{} : Bool}) -> {tc.mpok(Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))) == True{} : Bool}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          tc.put_case_mpok(Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.KMap.has(m, p))), m, hs, Tr.Ent{k, p, v}, mk)
        case Tr.Del{x}:
          match x:
            case 0n:
              mk
            case 1n++y:
              +F = Tr.KMap.ups(m, 1n+y, Nil{}, Tr.KMap.gl(m, 1n+y), Tr.KMap.gr(m, 1n+y))
              tc.drop_mpok(Tr.drops(F, hs, 1n+y), m, mk)
    case Tr.Rewind{+ops}:
      +n = Tr.KMap.patch(ops, hs, m)
      tc.keep_case_bst2(Tr.KMap.hangs(Tr.KMap.onto(n, Nil{}), n), m, n, mk, tc.patch_mpok(ops, hs, m, mk))

def tc.go_read(rs: List<&2, Tr.Rec>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {L.tc.bst(m) == True{} : Bool}, +mk: {tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.go(rs, hs, m)) == Tr.go(rs, Tr.KMap.read(m)) : List<&2, Tr.Ent>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> rest:
      +m2 = Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))
      +rr = tc.rec_read(m, hs, r, bt, mk, sd)
      +s2 = Equal.trans(Bool, Tr.sound(Tr.KMap.read(m2)), Tr.sound(Tr.apply(Tr.KMap.read(m), r)), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, z => Tr.sound(z), Tr.KMap.read(m2), Tr.apply(Tr.KMap.read(m), r), rr), apply_sound(Tr.KMap.read(m), sd, r))
      %rr : {Tr.KMap.read(Tr.KMap.go(rest, hs, m2)) == Tr.go(rest, _) : List<&2, Tr.Ent>}
      tc.go_read(rest, hs, m2, L.tc.rec_bst(m, hs, r, bt), tc.rec_mpok(m, hs, r, mk), s2)

def tc.note_fst(+log: List<&2, Tr.Rec>, +r: Tr.Rec, +hs: List<&2, Nat>, p: Tr.KMap & Tr.Ans) -> {Pair.fst(Tr.St, Tr.Ans, Tr.St.note(log, r, hs, p)) == Tr.St{Pair.fst(Tr.KMap, Tr.Ans, p), r <> log, hs} : Tr.St}:
  match p:
    case Tuple{a, b}:
      {==}

def tc.feed_go(rs: List<&2, Tr.Rec>, +m: Tr.KMap, +log: List<&2, Tr.Rec>, +hs: List<&2, Nat>) -> {Tr.core.feed.go(rs, Tr.St{m, log, hs}) == Tr.St{Tr.KMap.go(rs, hs, m), List.reverse.go(&2, Tr.Rec, rs, log), hs} : Tr.St}:
  match rs:
    case Nil{}:
      {==}
    case +r <> rest:
      +m2 = Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))
      %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.St.note(log, r, hs, Tr.KMap.rec(m, hs, r))), Tr.St{m2, r <> log, hs}, tc.note_fst(log, r, hs, Tr.KMap.rec(m, hs, r))) : {Tr.core.feed.go(rest, _) == Tr.St{Tr.KMap.go(rest, hs, m2), List.reverse.go(&2, Tr.Rec, rest, r <> log), hs} : Tr.St}
      tc.feed_go(rest, m2, r <> log, hs)

def tc.app_nil_rec(xs: List<&2, Tr.Rec>) -> {List.append(&2, Tr.Rec, xs, Nil{}) == xs : List<&2, Tr.Rec>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Tr.Rec>, List<&2, Tr.Rec>, ys => h <> ys, List.append(&2, Tr.Rec, t, Nil{}), t, tc.app_nil_rec(t))

def tc.rev_app(xs: List<&2, Tr.Rec>, +a: List<&2, Tr.Rec>, +b: List<&2, Tr.Rec>) -> {List.reverse.go(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, xs, a), b) == List.reverse.go(&2, Tr.Rec, a, List.append(&2, Tr.Rec, xs, b)) : List<&2, Tr.Rec>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      tc.rev_app(t, h <> a, b)

def tc.rev_rev(+xs: List<&2, Tr.Rec>) -> {List.reverse(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, xs, Nil{})) == xs : List<&2, Tr.Rec>}:
  Equal.trans(List<&2, Tr.Rec>, List.reverse.go(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, xs, Nil{}), Nil{}), List.append(&2, Tr.Rec, xs, Nil{}), xs, tc.rev_app(xs, Nil{}, Nil{}), tc.app_nil_rec(xs))

# the stepper after a journal
def tc.feed(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {Tr.core.feed(hs, rs) == Tr.St{Tr.KMap.go(rs, hs, Tr.KNil{}), List.reverse.go(&2, Tr.Rec, rs, Nil{}), hs} : Tr.St}:
  tc.feed_go(rs, Tr.KNil{}, Nil{}, hs)

def tc.live_read(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {Tr.KMap.read(Tr.KMap.go(rs, hs, Tr.KNil{})) == Tr.replay(rs) : List<&2, Tr.Ent>}:
  tc.go_read(rs, hs, Tr.KNil{}, {==}, {==}, {==})

def tc.live_bst(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {L.tc.bst(Tr.KMap.go(rs, hs, Tr.KNil{})) == True{} : Bool}:
  L.tc.go_bst(rs, hs, Tr.KNil{}, {==})

# the map after the first n records of the journal log of rs
def tc.at_read(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, +n: Nat) -> {Tr.KMap.read(Tr.St.at(List.reverse.go(&2, Tr.Rec, rs, Nil{}), hs, n)) == Tr.replay(List.take(&2, Tr.Rec, rs, n)) : List<&2, Tr.Ent>}:
  %Equal.sym(List<&2, Tr.Rec>, List.reverse(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, rs, Nil{})), rs, tc.rev_rev(rs)) : {Tr.KMap.read(Tr.KMap.go(List.take(&2, Tr.Rec, _, n), hs, Tr.KNil{})) == Tr.replay(List.take(&2, Tr.Rec, rs, n)) : List<&2, Tr.Ent>}
  tc.live_read(hs, List.take(&2, Tr.Rec, rs, n))

def pd.lt_add2(n: Nat) -> {Nat.is_lt(n, 2n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pd.lt_add2(p)

# The stack in the tree: order
# ----------------------------

# every key of t is less than m
def pd.lt_all(t: List<&2, Tr.Ent>, +m: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(rest, m))

def pd.lt_all_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +m: Nat, +ha: {pd.lt_all(A, m) == True{} : Bool}, hb: {pd.lt_all(B, m) == True{} : Bool}) -> {pd.lt_all(List.append(&2, Tr.Ent, A, B), m) == True{} : Bool}:
  match A:
    case Nil{}:
      hb
    case +e <> +r:
      L.tree.pt.and_t(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(List.append(&2, Tr.Ent, r, B), m), L.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(r, m), ha), pd.lt_all_app(r, B, m, L.tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(r, m), ha), hb))

# every key of encode(s) is at most twice the layers of s
def pd.enc_lt(s: List<&2, Dr.Layer>, +m: Nat, +h: {Nat.is_lt(Nat.double(List.length(&2, Dr.Layer, s)), m) == True{} : Bool}) -> {pd.lt_all(Dr.encode(s), m) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +hr = pt.lt_trans(Nat.double(n), 2n+Nat.double(n), m, pd.lt_add2(Nat.double(n)), h)
          +hx = pt.lt_trans(1n+Nat.double(n), 2n+Nat.double(n), m, L.pd.lt_succ(1n+Nat.double(n)), h)
          +hxy = L.tree.pt.and_t(Nat.is_lt(1n+Nat.double(n), m), Bool.and(Nat.is_lt(2n+Nat.double(n), m), True{}), hx, L.tree.pt.and_t(Nat.is_lt(2n+Nat.double(n), m), True{}, h, {==}))
          pd.lt_all_app(Dr.encode(rest), [x, y], m, pd.enc_lt(rest, m, hr), hxy)

def pd.above_app(+e: Tr.Ent, r: List<&2, Tr.Ent>, +x: Tr.Ent, +C: List<&2, Tr.Ent>, sa: {Tr.sorted(e <> r) == True{} : Bool}, la: {pd.lt_all(e <> r, Tr.Ent.k(x)) == True{} : Bool}) -> {Tr.above(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, x <> C)) == True{} : Bool}:
  match r:
    case Nil{}:
      L.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(x)), True{}, la)
    case +h <> +t:
      L.tree.pt.and_l(Tr.above(Tr.Ent.k(e), h <> t), Tr.sorted(h <> t), sa)

# a sorted list, then sorted nodes above all its keys, is sorted
def pd.sorted_snoc(A: List<&2, Tr.Ent>, +x: Tr.Ent, +C: List<&2, Tr.Ent>, +sa: {Tr.sorted(A) == True{} : Bool}, sc: {Tr.sorted(x <> C) == True{} : Bool}, +la: {pd.lt_all(A, Tr.Ent.k(x)) == True{} : Bool}) -> {Tr.sorted(List.append(&2, Tr.Ent, A, x <> C)) == True{} : Bool}:
  match A:
    case Nil{}:
      sc
    case +e <> +r:
      +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +lr = L.tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(x)), pd.lt_all(r, Tr.Ent.k(x)), la)
      L.tree.pt.and_t(Tr.above(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, x <> C)), Tr.sorted(List.append(&2, Tr.Ent, r, x <> C)), pd.above_app(e, r, x, C, sa, la), pd.sorted_snoc(r, x, C, sr, sc, lr))

def pd.enc_sorted(s: List<&2, Dr.Layer>) -> {Tr.sorted(Dr.encode(s)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +sxy = L.tree.pt.and_t(Nat.is_lt(1n+Nat.double(n), 2n+Nat.double(n)), Tr.sorted([y]), L.pd.lt_succ(1n+Nat.double(n)), {==})
          pd.sorted_snoc(Dr.encode(rest), x, [y], pd.enc_sorted(rest), sxy, pd.enc_lt(rest, 1n+Nat.double(n), L.pd.lt_succ(Nat.double(n))))

# The stack in the tree: parents
# ------------------------------

def pd.or_has_app(c: Bool, +all: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +p: Nat, o: {Bool.or(c, Tr.has(all, p)) == True{} : Bool}) -> {Bool.or(c, Tr.has(List.append(&2, Tr.Ent, all, C), p)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pt.has_app_l(all, C, p, o)

# a parent stays a parent when nodes come after
def pd.ok_app(+all: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +h: {Tr.ok(all, k, p) == True{} : Bool}) -> {Tr.ok(List.append(&2, Tr.Ent, all, C), k, p) == True{} : Bool}:
  +o = L.tree.pt.and_r(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(all, p)), h)
  L.tree.pt.and_t(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(List.append(&2, Tr.Ent, all, C), p)), L.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(all, p)), h), pd.or_has_app(Nat.is_eq(p, 0n), all, C, p, o))

def pd.rooted_app_all(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +rs: {Tr.rooted.go(s, all) == True{} : Bool}) -> {Tr.rooted.go(s, List.append(&2, Tr.Ent, all, C)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +he = L.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), rs)
      +hr = L.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), rs)
      L.tree.pt.and_t(Tr.ok(List.append(&2, Tr.Ent, all, C), Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, List.append(&2, Tr.Ent, all, C)), pd.ok_app(all, C, Tr.Ent.k(e), Tr.Ent.p(e), he), pd.rooted_app_all(r, all, C, hr))

def pd.rooted_go_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +ra: {Tr.rooted.go(A, all) == True{} : Bool}, rb: {Tr.rooted.go(B, all) == True{} : Bool}) -> {Tr.rooted.go(List.append(&2, Tr.Ent, A, B), all) == True{} : Bool}:
  match A:
    case Nil{}:
      rb
    case +e <> +r:
      +he = L.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), ra)
      +hr = L.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), ra)
      L.tree.pt.and_t(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(List.append(&2, Tr.Ent, r, B), all), he, pd.rooted_go_app(r, B, all, hr, rb))

# the kind node of the layer above rest hangs under the root (no layer
# below) or the kind node of the layer below
def pd.parent_ok(rest: List<&2, Dr.Layer>, +C: List<&2, Tr.Ent>) -> {Tr.ok(List.append(&2, Tr.Ent, Dr.encode(rest), C), Dr.kind.key(List.length(&2, Dr.Layer, rest)), Dr.kind.parent(List.length(&2, Dr.Layer, rest))) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case l2 <> +r2:
      match l2:
        case Dr.Layer{+k2, +b2}:
          +m = List.length(&2, Dr.Layer, r2)
          +E2 = Dr.encode(r2)
          +x2 = {Tr.Ent{1n+Nat.double(m), Dr.kind.parent(m), k2} : Tr.Ent}
          +y2 = {Tr.Ent{2n+Nat.double(m), 1n+Nat.double(m), b2} : Tr.Ent}
          +X2 = {[x2, y2] : List<&2, Tr.Ent>}
          +hh = pt.has_app_l(List.append(&2, Tr.Ent, E2, X2), C, 1n+Nat.double(m), pt.has_app_r(E2, X2, 1n+Nat.double(m), pt.has_head(x2, [y2])))
          L.tree.pt.and_t(Nat.is_lt(1n+Nat.double(m), 3n+Nat.double(m)), Bool.or(Nat.is_eq(1n+Nat.double(m), 0n), Tr.has(List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, E2, X2), C), 1n+Nat.double(m))), pd.lt_add2(1n+Nat.double(m)), pt.or_tr(Nat.is_eq(1n+Nat.double(m), 0n), Tr.has(List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, E2, X2), C), 1n+Nat.double(m)), hh))

def pd.enc_rooted(s: List<&2, Dr.Layer>) -> {Tr.rooted(Dr.encode(s)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +E = Dr.encode(rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +X = {[x, y] : List<&2, Tr.Ent>}
          +T = List.append(&2, Tr.Ent, E, X)
          +ra = pd.rooted_app_all(E, E, X, pd.enc_rooted(rest))
          +hy = L.tree.pt.and_t(Nat.is_lt(1n+Nat.double(n), 2n+Nat.double(n)), Bool.or(Nat.is_eq(1n+Nat.double(n), 0n), Tr.has(T, 1n+Nat.double(n))), L.pd.lt_succ(1n+Nat.double(n)), pt.or_tr(Nat.is_eq(1n+Nat.double(n), 0n), Tr.has(T, 1n+Nat.double(n)), pt.has_app_r(E, X, 1n+Nat.double(n), pt.has_head(x, [y]))))
          +rb = L.tree.pt.and_t(Tr.ok(T, 1n+Nat.double(n), Dr.kind.parent(n)), Bool.and(Tr.ok(T, 2n+Nat.double(n), 1n+Nat.double(n)), True{}), pd.parent_ok(rest, X), L.tree.pt.and_t(Tr.ok(T, 2n+Nat.double(n), 1n+Nat.double(n)), True{}, hy, {==}))
          pd.rooted_go_app(E, X, T, ra, rb)

def pd.dir_encode_sound(+s: List<&2, Dr.Layer>) -> {Tr.sound(Dr.encode(s)) == True{} : Bool}:
  L.tree.pt.and_t(Tr.sorted(Dr.encode(s)), Tr.rooted(Dr.encode(s)), pd.enc_sorted(s), pd.enc_rooted(s))

# ---- tree_ffi ----

# proof_tree_ffi: the laws of LAWS.bend section tree_ffi (the entry of
# bend/ffi_tree.bend). Round trip: each field reads back by the wire law
# wire_nat_round_trip, a tag picks its constructor, and the ops of a
# rewind read back item by item (tf.ops_rt, after the list lemmas of
# section wire). The entry laws rewrite the decoded ask into the entry;
# a step's reply splits its pair (tf.ans).

# the Nat round trip, turned for rewriting
def tf.rt(+n: Nat, +rest: String, h: {Laws.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Laws.wire_nat_round_trip(n, rest, h))

def tf.op_rt(o: Tr.Op, +rest: String, +h: {Laws.tree.op_fits(o) == True{} : Bool}) -> {Ft.get_op(Ft.put_op(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Tr.Op>}:
  match o:
    case Tr.Put{+k, +p, +v}:
      +O = {Tr.Put{k, p, v} : Tr.Op}
      +hpv = L.wr_and_r(Laws.wire_fits(k), Bool.and(Laws.wire_fits(p), Laws.wire_fits(v)), h)
      %tf.rt(0n, Wr.put_nat(k, Wr.put_nat(p, Wr.put_nat(v, rest))), {==}) : {Ft.get_op.go(_) == Wr.Got{O, rest} : Wr.Dec<Tr.Op>}
      %tf.rt(k, Wr.put_nat(p, Wr.put_nat(v, rest)), L.wr_and_l(Laws.wire_fits(k), Bool.and(Laws.wire_fits(p), Laws.wire_fits(v)), h)) : {Ft.get_op.put(_) == Wr.Got{O, rest} : Wr.Dec<Tr.Op>}
      %tf.rt(p, Wr.put_nat(v, rest), L.wr_and_l(Laws.wire_fits(p), Laws.wire_fits(v), hpv)) : {Ft.get_op.p(k, _) == Wr.Got{O, rest} : Wr.Dec<Tr.Op>}
      %tf.rt(v, rest, L.wr_and_r(Laws.wire_fits(p), Laws.wire_fits(v), hpv)) : {Ft.get_op.v(k, p, _) == Wr.Got{O, rest} : Wr.Dec<Tr.Op>}
      {==}
    case Tr.Del{+k}:
      %tf.rt(1n, Wr.put_nat(k, rest), {==}) : {Ft.get_op.go(_) == Wr.Got{Tr.Del{k}, rest} : Wr.Dec<Tr.Op>}
      %tf.rt(k, rest, h) : {Ft.get_op.del(_) == Wr.Got{Tr.Del{k}, rest} : Wr.Dec<Tr.Op>}
      {==}

# the ops of a rewind
# ------------------

def tf.fit_l(+o: Tr.Op, -ops: List<&2, Tr.Op>, h: {Laws.tree.ops_fit(o <> ops) == True{} : Bool}) -> {Laws.tree.op_fits(o) == True{} : Bool}:
  L.wr_and_l(Laws.tree.op_fits(o), Laws.tree.ops_fit(ops), h)

def tf.fit_r(+o: Tr.Op, -ops: List<&2, Tr.Op>, h: {Laws.tree.ops_fit(o <> ops) == True{} : Bool}) -> {Laws.tree.ops_fit(ops) == True{} : Bool}:
  L.wr_and_r(Laws.tree.op_fits(o), Laws.tree.ops_fit(ops), h)

# the items of a list of ops, then rest
def tf.items(ops: List<&2, Tr.Op>, rest: String) -> String:
  match ops:
    case Nil{}:
      rest
    case o <> r:
      Ft.put_op(o, tf.items(r, rest))

def tf.go(ops: List<&2, Tr.Op>, +rest: String) -> {Wr.put_list.go(~Tr.Op, ~Ft.put_op, ops, rest) == (List.length(&2, Tr.Op, ops), tf.items(ops, rest)) : Nat & String}:
  match ops:
    case Nil{}:
      {==}
    case +o <> +r:
      %Equal.sym(Nat & String, Wr.put_list.go(~Tr.Op, ~Ft.put_op, r, rest), (List.length(&2, Tr.Op, r), tf.items(r, rest)), tf.go(r, rest)) : {Wr.put_list.step(~Tr.Op, ~Ft.put_op, o, _) == (1n+List.length(&2, Tr.Op, r), Ft.put_op(o, tf.items(r, rest))) : Nat & String}
      {==}

# a list of ops is its count, then its items
def tf.put_list(+ops: List<&2, Tr.Op>, +rest: String) -> {Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest) == Wr.put_nat(List.length(&2, Tr.Op, ops), tf.items(ops, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~Tr.Op, ~Ft.put_op, ops, rest), (List.length(&2, Tr.Op, ops), tf.items(ops, rest)), tf.go(ops, rest))

def tf.list_go(ops: List<&2, Tr.Op>, +o: Tr.Op, +rest: String, +hf: {Laws.tree.ops_fit(o <> ops) == True{} : Bool}) -> {Wr.get_list.go(~Tr.Op, ~Ft.get_op, List.length(&2, Tr.Op, ops), Ft.get_op(Ft.put_op(o, tf.items(ops, rest)))) == Wr.Got{o <> ops, rest} : Wr.Dec<List<&2, Tr.Op>>}:
  match ops:
    case Nil{}:
      %Equal.sym(Wr.Dec<Tr.Op>, Ft.get_op(Ft.put_op(o, rest)), Wr.Got{o, rest}, tf.op_rt(o, rest, tf.fit_l(o, Nil{}, hf))) : {Wr.get_list.go(~Tr.Op, ~Ft.get_op, 0n, _) == Wr.Got{[o], rest} : Wr.Dec<List<&2, Tr.Op>>}
      {==}
    case +o2 <> +ops2:
      %Equal.sym(Wr.Dec<Tr.Op>, Ft.get_op(Ft.put_op(o, tf.items(o2 <> ops2, rest))), Wr.Got{o, tf.items(o2 <> ops2, rest)}, tf.op_rt(o, tf.items(o2 <> ops2, rest), tf.fit_l(o, o2 <> ops2, hf))) : {Wr.get_list.go(~Tr.Op, ~Ft.get_op, 1n+List.length(&2, Tr.Op, ops2), _) == Wr.Got{o <> o2 <> ops2, rest} : Wr.Dec<List<&2, Tr.Op>>}
      %Equal.sym(Wr.Dec<List<&2, Tr.Op>>, Wr.get_list.go(~Tr.Op, ~Ft.get_op, List.length(&2, Tr.Op, ops2), Ft.get_op(Ft.put_op(o2, tf.items(ops2, rest)))), Wr.Got{o2 <> ops2, rest}, tf.list_go(ops2, o2, rest, tf.fit_r(o, o2 <> ops2, hf))) : {Wr.get_list.cons(Tr.Op, o, _) == Wr.Got{o <> o2 <> ops2, rest} : Wr.Dec<List<&2, Tr.Op>>}
      {==}

def tf.list_start(ops: List<&2, Tr.Op>, +rest: String, +hf: {Laws.tree.ops_fit(ops) == True{} : Bool}) -> {Wr.get_list.start(~Tr.Op, ~Ft.get_op, Wr.Got{List.length(&2, Tr.Op, ops), tf.items(ops, rest)}) == Wr.Got{ops, rest} : Wr.Dec<List<&2, Tr.Op>>}:
  match ops:
    case Nil{}:
      {==}
    case +o <> +r:
      tf.list_go(r, o, rest, hf)

# a list of ops that fits reads back
def tf.ops_rt(+ops: List<&2, Tr.Op>, +rest: String, hl: {Laws.wire_fits(List.length(&2, Tr.Op, ops)) == True{} : Bool}, +hf: {Laws.tree.ops_fit(ops) == True{} : Bool}) -> {Wr.get_list(~Tr.Op, ~Ft.get_op, Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest)) == Wr.Got{ops, rest} : Wr.Dec<List<&2, Tr.Op>>}:
  %Equal.sym(String, Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest), Wr.put_nat(List.length(&2, Tr.Op, ops), tf.items(ops, rest)), tf.put_list(ops, rest)) : {Wr.get_list(~Tr.Op, ~Ft.get_op, _) == Wr.Got{ops, rest} : Wr.Dec<List<&2, Tr.Op>>}
  %tf.rt(List.length(&2, Tr.Op, ops), tf.items(ops, rest), hl) : {Wr.get_list.start(~Tr.Op, ~Ft.get_op, _) == Wr.Got{ops, rest} : Wr.Dec<List<&2, Tr.Op>>}
  tf.list_start(ops, rest, hf)

# an ask
# ------

def tf.ask_rt(q: Tr.Ask, +rest: String, +h: {Laws.tree.ask_fits(q) == True{} : Bool}) -> {Ft.get_ask(Ft.put_ask(q, rest)) == Wr.Got{q, rest} : Wr.Dec<Tr.Ask>}:
  match q:
    case Tr.Note{r}:
      match r:
        case Tr.Do{+o}:
          +Q = {Tr.Note{Tr.Do{o}} : Tr.Ask}
          %tf.rt(0n, Wr.put_nat(0n, Ft.put_op(o, rest)), {==}) : {Ft.get_ask.go(_) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          %tf.rt(0n, Ft.put_op(o, rest), {==}) : {Ft.get_ask.note(Ft.get_rec.go(_)) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          %Equal.sym(Wr.Dec<Tr.Op>, Ft.get_op(Ft.put_op(o, rest)), Wr.Got{o, rest}, tf.op_rt(o, rest, h)) : {Ft.get_ask.note(Ft.get_rec.do(_)) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          {==}
        case Tr.Rewind{+ops}:
          +Q = {Tr.Note{Tr.Rewind{ops}} : Tr.Ask}
          +s2 = Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest)
          %tf.rt(0n, Wr.put_nat(1n, s2), {==}) : {Ft.get_ask.go(_) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          %tf.rt(1n, s2, {==}) : {Ft.get_ask.note(Ft.get_rec.go(_)) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          %Equal.sym(Wr.Dec<List<&2, Tr.Op>>, Wr.get_list(~Tr.Op, ~Ft.get_op, s2), Wr.Got{ops, rest}, tf.ops_rt(ops, rest, L.wr_and_l(Laws.wire_fits(List.length(&2, Tr.Op, ops)), Laws.tree.ops_fit(ops), h), L.wr_and_r(Laws.wire_fits(List.length(&2, Tr.Op, ops)), Laws.tree.ops_fit(ops), h))) : {Ft.get_ask.note(Ft.get_rec.rewind(_)) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          {==}
    case Tr.Plan{+n}:
      %tf.rt(1n, Wr.put_nat(n, rest), {==}) : {Ft.get_ask.go(_) == Wr.Got{Tr.Plan{n}, rest} : Wr.Dec<Tr.Ask>}
      %tf.rt(n, rest, h) : {Ft.get_ask.plan(_) == Wr.Got{Tr.Plan{n}, rest} : Wr.Dec<Tr.Ask>}
      {==}
    case Tr.Snap{+n}:
      %tf.rt(2n, Wr.put_nat(n, rest), {==}) : {Ft.get_ask.go(_) == Wr.Got{Tr.Snap{n}, rest} : Wr.Dec<Tr.Ask>}
      %tf.rt(n, rest, h) : {Ft.get_ask.snap(_) == Wr.Got{Tr.Snap{n}, rest} : Wr.Dec<Tr.Ask>}
      {==}
