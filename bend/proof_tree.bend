# proof_tree: the session tree laws of LAWS.bend (S1), about bend/tree.bend.
#
# Lookups first: a set or an unset changes only the lookup of its own key
# (`pt.get_set_*`, `pt.get_unset_*`), and both keep a tree sorted. A put
# keeps every parent (`pt.ok_set`); a delete keeps the parent of every
# node it keeps (`pt.rooted_prune_go`, by the nodes walked so far: kept,
# or with their key gone). So every record keeps a tree sound
# (`apply_sound`). A rewind's lookup at a key follows its ops on that key
# (`pt.look`); so after diff(a, b) the tree agrees with b on every key,
# and two sorted trees that agree are equal (`pt.ext`). A delete of the
# root (key 0) changes nothing, and no node of a rooted tree is the root
# (`pt.rooted_nz`); a delete of a node removes it and its subtree only.

import Base
import ./tree.bend as T

# Logic
# -----

def pt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pt.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pt.BD(_, Unit, A)
  Unit{}

def pt.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pt.BD(_, A, Unit)
  Unit{}

def pt.MD(m: Maybe<&2, T.Ent>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

def pt.none_some(-A: Type, -x: T.Ent, e: {None{} == Some{x} : Maybe<&2, T.Ent>}) -> A:
  %e : pt.MD(_, Unit, A)
  Unit{}

def pt.some_none(-A: Type, -x: T.Ent, e: {Some{x} == None{} : Maybe<&2, T.Ent>}) -> A:
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

def pt.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pt.absurdF({False{} == True{} : Bool}, h)

def pt.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pt.absurdF({b == True{} : Bool}, h)

def pt.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pt.or_l(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      pt.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pt.or_r(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      pt.absurd({b == False{} : Bool}, h)
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
  pt.absurd(Empty, Equal.trans(Bool, True{}, a, False{}, Equal.sym(Bool, a, True{}, h), g))

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
      pt.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pt.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pt.eq_true(p, q, h))

def pt.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pt.eq_comm(p, q)

def pt.ne_comm(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  %pt.eq_comm(a, b) : {_ == False{} : Bool}
  h

def pt.lt_irrefl(k: Nat) -> {Nat.is_lt(k, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pt.lt_irrefl(p)

def pt.lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      pt.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      pt.absurdF({Nat.is_lt(a, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      pt.lt_trans(p, q, r, ab, bc)

# a key below another is not it
def pt.lt_ne(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case _ 0n:
      pt.absurdF({Nat.is_eq(a, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pt.lt_ne(p, q, h)

def pt.lt_ne_r(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  pt.ne_comm(a, b, pt.lt_ne(a, b, h))

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

def pt.ent_eta(e: T.Ent) -> {T.Ent{T.Ent.k(e), T.Ent.p(e), T.Ent.v(e)} == e : T.Ent}:
  match e:
    case T.Ent{k, p, v}:
      {==}

def pt.ent_refl(e: T.Ent) -> {T.Ent.eq(e, e) == True{} : Bool}:
  match e:
    case T.Ent{+k, +p, +v}:
      %pt.eq_refl(k) : {Bool.and(_, Bool.and(Nat.is_eq(p, p), Nat.is_eq(v, v))) == True{} : Bool}
      %pt.eq_refl(p) : {Bool.and(True{}, Bool.and(_, Nat.is_eq(v, v))) == True{} : Bool}
      %pt.eq_refl(v) : {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
      {==}

def pt.ent_true(a: T.Ent, b: T.Ent, +h: {T.Ent.eq(a, b) == True{} : Bool}) -> {a == b : T.Ent}:
  match a b:
    case T.Ent{+ak, +ap, +av} T.Ent{+bk, +bp, +bv}:
      +hk = pt.eq_true(ak, bk, pt.and_l(Nat.is_eq(ak, bk), Bool.and(Nat.is_eq(ap, bp), Nat.is_eq(av, bv)), h))
      +h2 = pt.and_r(Nat.is_eq(ak, bk), Bool.and(Nat.is_eq(ap, bp), Nat.is_eq(av, bv)), h)
      +hp = pt.eq_true(ap, bp, pt.and_l(Nat.is_eq(ap, bp), Nat.is_eq(av, bv), h2))
      +hv = pt.eq_true(av, bv, pt.and_r(Nat.is_eq(ap, bp), Nat.is_eq(av, bv), h2))
      %hk : {T.Ent{ak, ap, av} == T.Ent{_, bp, bv} : T.Ent}
      %hp : {T.Ent{ak, ap, av} == T.Ent{ak, _, bv} : T.Ent}
      %hv : {T.Ent{ak, ap, av} == T.Ent{ak, ap, _} : T.Ent}
      {==}

# a lookup that is the same as Some{e} is Some{e}
def pt.same_some(m: Maybe<&2, T.Ent>, +e: T.Ent, h: {T.same(m, Some{e}) == True{} : Bool}) -> {m == Some{e} : Maybe<&2, T.Ent>}:
  match m:
    case None{}:
      pt.absurdF({None{} == Some{e} : Maybe<&2, T.Ent>}, h)
    case Some{x}:
      Equal.cong(T.Ent, Maybe<&2, T.Ent>, y => Some{y}, x, e, pt.ent_true(x, e, h))

def pt.same_refl(+e: T.Ent) -> {T.same(Some{e}, Some{e}) == True{} : Bool}:
  pt.ent_refl(e)

# Lookup
# ------

def pt.get_hit(+h: T.Ent, +r: List<&2, T.Ent>, +x: Nat, eq: {Nat.is_eq(T.Ent.k(h), x) == True{} : Bool}) -> {T.get(h <> r, x) == Some{h} : Maybe<&2, T.Ent>}:
  %Equal.sym(Bool, Nat.is_eq(T.Ent.k(h), x), True{}, eq) : {T.get.go(h <> r, x, _) == Some{h} : Maybe<&2, T.Ent>}
  {==}

def pt.get_head(+h: T.Ent, +r: List<&2, T.Ent>) -> {T.get(h <> r, T.Ent.k(h)) == Some{h} : Maybe<&2, T.Ent>}:
  pt.get_hit(h, r, T.Ent.k(h), Equal.sym(Bool, True{}, Nat.is_eq(T.Ent.k(h), T.Ent.k(h)), pt.eq_refl(T.Ent.k(h))))

def pt.get_miss(+h: T.Ent, +r: List<&2, T.Ent>, +x: Nat, ne: {Nat.is_eq(T.Ent.k(h), x) == False{} : Bool}) -> {T.get(h <> r, x) == T.get(r, x) : Maybe<&2, T.Ent>}:
  %Equal.sym(Bool, Nat.is_eq(T.Ent.k(h), x), False{}, ne) : {T.get.go(h <> r, x, _) == T.get(r, x) : Maybe<&2, T.Ent>}
  {==}

def pt.get_go_cong(b: Bool, +h: T.Ent, +s: List<&2, T.Ent>, +r: List<&2, T.Ent>, +x: Nat, e: {T.get(s, x) == T.get(r, x) : Maybe<&2, T.Ent>}) -> {T.get.go(h <> s, x, b) == T.get.go(h <> r, x, b) : Maybe<&2, T.Ent>}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

# a lookup sees past a head that agrees
def pt.get_cons_cong(+h: T.Ent, +s: List<&2, T.Ent>, +r: List<&2, T.Ent>, +x: Nat, e: {T.get(s, x) == T.get(r, x) : Maybe<&2, T.Ent>}) -> {T.get(h <> s, x) == T.get(h <> r, x) : Maybe<&2, T.Ent>}:
  pt.get_go_cong(Nat.is_eq(T.Ent.k(h), x), h, s, r, x, e)

def pt.get_set_go_same(t: List<&2, T.Ent>, +e: T.Ent, c: Cmp, ec: {T.first(T.Ent.k(e), t) == c : Cmp}) -> {T.get(T.set.go(t, e, c), T.Ent.k(e)) == Some{e} : Maybe<&2, T.Ent>}:
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
          +s = T.set.go(r, e, T.first(T.Ent.k(e), r))
          +ne = pt.lt_ne(T.Ent.k(h), T.Ent.k(e), pt.cmp_gt(T.Ent.k(e), T.Ent.k(h), ec))
          Equal.trans(Maybe<&2, T.Ent>, T.get(h <> s, T.Ent.k(e)), T.get(s, T.Ent.k(e)), Some{e}, pt.get_miss(h, s, T.Ent.k(e), ne), pt.get_set_go_same(r, e, T.first(T.Ent.k(e), r), {==}))

def pt.get_set_same(+t: List<&2, T.Ent>, +e: T.Ent) -> {T.get(T.set(t, e), T.Ent.k(e)) == Some{e} : Maybe<&2, T.Ent>}:
  pt.get_set_go_same(t, e, T.first(T.Ent.k(e), t), {==})

def pt.get_set_go_other(t: List<&2, T.Ent>, +e: T.Ent, c: Cmp, ec: {T.first(T.Ent.k(e), t) == c : Cmp}, +x: Nat, +ne: {Nat.is_eq(T.Ent.k(e), x) == False{} : Bool}) -> {T.get(T.set.go(t, e, c), x) == T.get(t, x) : Maybe<&2, T.Ent>}:
  match t:
    case Nil{}:
      pt.get_miss(e, Nil{}, x, ne)
    case +h <> +r:
      match c:
        case LT{}:
          pt.get_miss(e, h <> r, x, ne)
        case EQ{}:
          +keq = pt.cmp_eq(T.Ent.k(e), T.Ent.k(h), ec)
          %keq : {T.get(e <> r, x) == T.get.go(h <> r, x, Nat.is_eq(_, x)) : Maybe<&2, T.Ent>}
          %Equal.sym(Bool, Nat.is_eq(T.Ent.k(e), x), False{}, ne) : {T.get.go(e <> r, x, _) == T.get.go(h <> r, x, _) : Maybe<&2, T.Ent>}
          {==}
        case GT{}:
          pt.get_cons_cong(h, T.set.go(r, e, T.first(T.Ent.k(e), r)), r, x, pt.get_set_go_other(r, e, T.first(T.Ent.k(e), r), {==}, x, ne))

def pt.get_set_other(+t: List<&2, T.Ent>, +e: T.Ent, +x: Nat, ne: {Nat.is_eq(T.Ent.k(e), x) == False{} : Bool}) -> {T.get(T.set(t, e), x) == T.get(t, x) : Maybe<&2, T.Ent>}:
  pt.get_set_go_other(t, e, T.first(T.Ent.k(e), t), {==}, x, ne)

def pt.get_unset_go_same(t: List<&2, T.Ent>, +x: Nat, hit: Bool, eh: {T.key.at(t, x) == hit : Bool}) -> {T.get(T.unset.go(t, x, hit), x) == None{} : Maybe<&2, T.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.get_unset_go_same(r, x, T.key.at(r, x), {==})
        case False{}:
          +u = T.unset.go(r, x, T.key.at(r, x))
          Equal.trans(Maybe<&2, T.Ent>, T.get(h <> u, x), T.get(u, x), None{}, pt.get_miss(h, u, x, eh), pt.get_unset_go_same(r, x, T.key.at(r, x), {==}))

def pt.get_unset_same(+t: List<&2, T.Ent>, +x: Nat) -> {T.get(T.unset(t, x), x) == None{} : Maybe<&2, T.Ent>}:
  pt.get_unset_go_same(t, x, T.key.at(t, x), {==})

def pt.ne_at(+a: Nat, +y: Nat, +x: Nat, ay: {a == y : Nat}, ne: {Nat.is_eq(y, x) == False{} : Bool}) -> {Nat.is_eq(a, x) == False{} : Bool}:
  %Equal.sym(Nat, a, y, ay) : {Nat.is_eq(_, x) == False{} : Bool}
  ne

def pt.get_unset_go_other(t: List<&2, T.Ent>, +y: Nat, hit: Bool, eh: {T.key.at(t, y) == hit : Bool}, +x: Nat, +ne: {Nat.is_eq(y, x) == False{} : Bool}) -> {T.get(T.unset.go(t, y, hit), x) == T.get(t, x) : Maybe<&2, T.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +neh = pt.ne_at(T.Ent.k(h), y, x, pt.eq_true(T.Ent.k(h), y, eh), ne)
          +u = T.unset.go(r, y, T.key.at(r, y))
          Equal.trans(Maybe<&2, T.Ent>, T.get(u, x), T.get(r, x), T.get(h <> r, x), pt.get_unset_go_other(r, y, T.key.at(r, y), {==}, x, ne), Equal.sym(Maybe<&2, T.Ent>, T.get(h <> r, x), T.get(r, x), pt.get_miss(h, r, x, neh)))
        case False{}:
          pt.get_cons_cong(h, T.unset.go(r, y, T.key.at(r, y)), r, x, pt.get_unset_go_other(r, y, T.key.at(r, y), {==}, x, ne))

def pt.get_unset_other(+t: List<&2, T.Ent>, +y: Nat, +x: Nat, ne: {Nat.is_eq(y, x) == False{} : Bool}) -> {T.get(T.unset(t, y), x) == T.get(t, x) : Maybe<&2, T.Ent>}:
  pt.get_unset_go_other(t, y, T.key.at(t, y), {==}, x, ne)

# Order
# -----

def pt.above_set_go(t: List<&2, T.Ent>, +e: T.Ent, c: Cmp, +l: Nat, al: {T.above(l, t) == True{} : Bool}, le: {Nat.is_lt(l, T.Ent.k(e)) == True{} : Bool}) -> {T.above(l, T.set.go(t, e, c)) == True{} : Bool}:
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

def pt.sorted_set_go(t: List<&2, T.Ent>, +e: T.Ent, c: Cmp, ec: {T.first(T.Ent.k(e), t) == c : Cmp}, +st: {T.sorted(t) == True{} : Bool}) -> {T.sorted(T.set.go(t, e, c)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match c:
        case LT{}:
          pt.and_t(Nat.is_lt(T.Ent.k(e), T.Ent.k(h)), T.sorted(h <> r), pt.cmp_lt(T.Ent.k(e), T.Ent.k(h), ec), st)
        case EQ{}:
          %Equal.sym(Nat, T.Ent.k(e), T.Ent.k(h), pt.cmp_eq(T.Ent.k(e), T.Ent.k(h), ec)) : {Bool.and(T.above(_, r), T.sorted(r)) == True{} : Bool}
          st
        case GT{}:
          +s = T.set.go(r, e, T.first(T.Ent.k(e), r))
          +al = pt.and_l(T.above(T.Ent.k(h), r), T.sorted(r), st)
          +sr = pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st)
          pt.and_t(T.above(T.Ent.k(h), s), T.sorted(s), pt.above_set_go(r, e, T.first(T.Ent.k(e), r), T.Ent.k(h), al, pt.cmp_gt(T.Ent.k(e), T.Ent.k(h), ec)), pt.sorted_set_go(r, e, T.first(T.Ent.k(e), r), {==}, sr))

def pt.above_tail(+l: Nat, +h: T.Ent, r: List<&2, T.Ent>, al: {T.above(l, h <> r) == True{} : Bool}, st: {T.sorted(h <> r) == True{} : Bool}) -> {T.above(l, r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +h2 <> +r2:
      pt.lt_trans(l, T.Ent.k(h), T.Ent.k(h2), al, pt.and_l(Nat.is_lt(T.Ent.k(h), T.Ent.k(h2)), T.sorted(h2 <> r2), st))

def pt.above_unset_go(t: List<&2, T.Ent>, +x: Nat, hit: Bool, +l: Nat, al: {T.above(l, t) == True{} : Bool}, +st: {T.sorted(t) == True{} : Bool}) -> {T.above(l, T.unset.go(t, x, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.above_unset_go(r, x, T.key.at(r, x), l, pt.above_tail(l, h, r, al, st), pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st))
        case False{}:
          al

def pt.sorted_unset_go(t: List<&2, T.Ent>, +x: Nat, hit: Bool, +st: {T.sorted(t) == True{} : Bool}) -> {T.sorted(T.unset.go(t, x, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.sorted_unset_go(r, x, T.key.at(r, x), pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st))
        case False{}:
          +sr = pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st)
          +u = T.unset.go(r, x, T.key.at(r, x))
          pt.and_t(T.above(T.Ent.k(h), u), T.sorted(u), pt.above_unset_go(r, x, T.key.at(r, x), T.Ent.k(h), pt.and_l(T.above(T.Ent.k(h), r), T.sorted(r), st), sr), pt.sorted_unset_go(r, x, T.key.at(r, x), sr))

def pt.sorted_exact(+t: List<&2, T.Ent>, o: T.Op, st: {T.sorted(t) == True{} : Bool}) -> {T.sorted(T.exact(t, o)) == True{} : Bool}:
  match o:
    case T.Put{+k, +p, +v}:
      pt.sorted_set_go(t, T.Ent{k, p, v}, T.first(k, t), {==}, st)
    case T.Del{+x}:
      pt.sorted_unset_go(t, x, T.key.at(t, x), st)

def pt.sorted_patch(ops: List<&2, T.Op>, +t: List<&2, T.Ent>, st: {T.sorted(t) == True{} : Bool}) -> {T.sorted(T.patch(ops, t)) == True{} : Bool}:
  match ops:
    case Nil{}:
      st
    case +o <> rest:
      pt.sorted_patch(rest, T.exact(t, o), pt.sorted_exact(t, o, st))

# Membership
# ----------

def pt.void(-A: Type, e: Empty) -> A:
  match e:

def pt.or_false_r(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
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

def pt.has_cons_go(b: Bool, +h: T.Ent, +r: List<&2, T.Ent>, +y: Nat) -> {Maybe.is_some(&2, T.Ent, T.get.go(h <> r, y, b)) == Bool.or(b, T.has(r, y)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pt.has_cons(+h: T.Ent, +r: List<&2, T.Ent>, +y: Nat) -> {T.has(h <> r, y) == Bool.or(Nat.is_eq(T.Ent.k(h), y), T.has(r, y)) : Bool}:
  pt.has_cons_go(Nat.is_eq(T.Ent.k(h), y), h, r, y)

def pt.has_miss(+h: T.Ent, +r: List<&2, T.Ent>, +y: Nat, ne: {Nat.is_eq(T.Ent.k(h), y) == False{} : Bool}) -> {T.has(h <> r, y) == T.has(r, y) : Bool}:
  Equal.cong(Maybe<&2, T.Ent>, Bool, m => Maybe.is_some(&2, T.Ent, m), T.get(h <> r, y), T.get(r, y), pt.get_miss(h, r, y, ne))

def pt.has_head(+h: T.Ent, +r: List<&2, T.Ent>) -> {T.has(h <> r, T.Ent.k(h)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, T.Ent>, T.get(h <> r, T.Ent.k(h)), Some{h}, pt.get_head(h, r)) : {Maybe.is_some(&2, T.Ent, _) == True{} : Bool}
  {==}

def pt.has_app(A: List<&2, T.Ent>, +C: List<&2, T.Ent>, +y: Nat) -> {T.has(List.append(&2, T.Ent, A, C), y) == Bool.or(T.has(A, y), T.has(C, y)) : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +ea = Nat.is_eq(T.Ent.k(a), y)
      +rc = List.append(&2, T.Ent, r, C)
      %Equal.sym(Bool, T.has(a <> rc, y), Bool.or(ea, T.has(rc, y)), pt.has_cons(a, rc, y)) : {_ == Bool.or(T.has(a <> r, y), T.has(C, y)) : Bool}
      %Equal.sym(Bool, T.has(rc, y), Bool.or(T.has(r, y), T.has(C, y)), pt.has_app(r, C, y)) : {Bool.or(ea, _) == Bool.or(T.has(a <> r, y), T.has(C, y)) : Bool}
      %Equal.sym(Bool, T.has(a <> r, y), Bool.or(ea, T.has(r, y)), pt.has_cons(a, r, y)) : {Bool.or(ea, Bool.or(T.has(r, y), T.has(C, y))) == Bool.or(_, T.has(C, y)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(ea, T.has(r, y)), T.has(C, y)), Bool.or(ea, Bool.or(T.has(r, y), T.has(C, y))), pt.or_assoc(ea, T.has(r, y), T.has(C, y)))

def pt.has_app_l(+A: List<&2, T.Ent>, +C: List<&2, T.Ent>, +y: Nat, h: {T.has(A, y) == True{} : Bool}) -> {T.has(List.append(&2, T.Ent, A, C), y) == True{} : Bool}:
  %Equal.sym(Bool, T.has(List.append(&2, T.Ent, A, C), y), Bool.or(T.has(A, y), T.has(C, y)), pt.has_app(A, C, y)) : {_ == True{} : Bool}
  pt.or_tl(T.has(A, y), T.has(C, y), h)

def pt.has_app_r(+A: List<&2, T.Ent>, +C: List<&2, T.Ent>, +y: Nat, h: {T.has(C, y) == True{} : Bool}) -> {T.has(List.append(&2, T.Ent, A, C), y) == True{} : Bool}:
  %Equal.sym(Bool, T.has(List.append(&2, T.Ent, A, C), y), Bool.or(T.has(A, y), T.has(C, y)), pt.has_app(A, C, y)) : {_ == True{} : Bool}
  pt.or_tr(T.has(A, y), T.has(C, y), h)

# no node of a sorted list is below its first key
def pt.has_below(X: List<&2, T.Ent>, +y: Nat, +al: {T.above(y, X) == True{} : Bool}, +st: {T.sorted(X) == True{} : Bool}) -> {T.has(X, y) == False{} : Bool}:
  match X:
    case Nil{}:
      {==}
    case +h <> +r:
      Equal.trans(Bool, T.has(h <> r, y), T.has(r, y), False{}, pt.has_miss(h, r, y, pt.lt_ne_r(y, T.Ent.k(h), al)), pt.has_below(r, y, pt.above_tail(y, h, r, al, st), pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st)))

def pt.app_snoc(A: List<&2, T.Ent>, +e: T.Ent, +C: List<&2, T.Ent>) -> {List.append(&2, T.Ent, List.append(&2, T.Ent, A, [e]), C) == List.append(&2, T.Ent, A, e <> C) : List<&2, T.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      Equal.cong(List<&2, T.Ent>, List<&2, T.Ent>, l => a <> l, List.append(&2, T.Ent, List.append(&2, T.Ent, r, [e]), C), List.append(&2, T.Ent, r, e <> C), pt.app_snoc(r, e, C))

def pt.sorted_app_r(A: List<&2, T.Ent>, +C: List<&2, T.Ent>, st: {T.sorted(List.append(&2, T.Ent, A, C)) == True{} : Bool}) -> {T.sorted(C) == True{} : Bool}:
  match A:
    case Nil{}:
      st
    case +a <> +r:
      pt.sorted_app_r(r, C, pt.and_r(T.above(T.Ent.k(a), List.append(&2, T.Ent, r, C)), T.sorted(List.append(&2, T.Ent, r, C)), st))

# A put
# -----

def pt.has_set_go(+t: List<&2, T.Ent>, +e: T.Ent, +y: Nat, b: Bool, eb: {Nat.is_eq(T.Ent.k(e), y) == b : Bool}, h: {T.has(t, y) == True{} : Bool}) -> {T.has(T.set(t, e), y) == True{} : Bool}:
  match b:
    case True{}:
      %pt.eq_true(T.Ent.k(e), y, eb) : {T.has(T.set(t, e), _) == True{} : Bool}
      %Equal.sym(Maybe<&2, T.Ent>, T.get(T.set(t, e), T.Ent.k(e)), Some{e}, pt.get_set_same(t, e)) : {Maybe.is_some(&2, T.Ent, _) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, T.Ent>, T.get(T.set(t, e), y), T.get(t, y), pt.get_set_other(t, e, y, eb)) : {Maybe.is_some(&2, T.Ent, _) == True{} : Bool}
      h

# a set keeps every node there
def pt.has_set(+t: List<&2, T.Ent>, +e: T.Ent, +y: Nat, h: {T.has(t, y) == True{} : Bool}) -> {T.has(T.set(t, e), y) == True{} : Bool}:
  pt.has_set_go(t, e, y, Nat.is_eq(T.Ent.k(e), y), {==}, h)

def pt.or_has_set(b: Bool, +t: List<&2, T.Ent>, +e: T.Ent, +p: Nat, o: {Bool.or(b, T.has(t, p)) == True{} : Bool}) -> {Bool.or(b, T.has(T.set(t, e), p)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pt.has_set(t, e, p, o)

def pt.ok_set(+t: List<&2, T.Ent>, +e: T.Ent, +k: Nat, +p: Nat, +h: {T.ok(t, k, p) == True{} : Bool}) -> {T.ok(T.set(t, e), k, p) == True{} : Bool}:
  +o = pt.and_r(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), T.has(t, p)), h)
  pt.and_t(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), T.has(T.set(t, e), p)), pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), T.has(t, p)), h), pt.or_has_set(Nat.is_eq(p, 0n), t, e, p, o))

def pt.rooted_mono_set(s: List<&2, T.Ent>, +all: List<&2, T.Ent>, +e: T.Ent, +rs: {T.rooted.go(s, all) == True{} : Bool}) -> {T.rooted.go(s, T.set(all, e)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +h <> +r:
      +oh = pt.and_l(T.ok(all, T.Ent.k(h), T.Ent.p(h)), T.rooted.go(r, all), rs)
      +rr = pt.and_r(T.ok(all, T.Ent.k(h), T.Ent.p(h)), T.rooted.go(r, all), rs)
      pt.and_t(T.ok(T.set(all, e), T.Ent.k(h), T.Ent.p(h)), T.rooted.go(r, T.set(all, e)), pt.ok_set(all, e, T.Ent.k(h), T.Ent.p(h), oh), pt.rooted_mono_set(r, all, e, rr))

def pt.rooted_set_go(s: List<&2, T.Ent>, +all: List<&2, T.Ent>, +e: T.Ent, c: Cmp, +rs: {T.rooted.go(s, all) == True{} : Bool}, +oe: {T.ok(all, T.Ent.k(e), T.Ent.p(e)) == True{} : Bool}) -> {T.rooted.go(T.set.go(s, e, c), T.set(all, e)) == True{} : Bool}:
  match s:
    case Nil{}:
      pt.and_t(T.ok(T.set(all, e), T.Ent.k(e), T.Ent.p(e)), True{}, pt.ok_set(all, e, T.Ent.k(e), T.Ent.p(e), oe), {==})
    case +h <> +r:
      match c:
        case LT{}:
          pt.and_t(T.ok(T.set(all, e), T.Ent.k(e), T.Ent.p(e)), T.rooted.go(h <> r, T.set(all, e)), pt.ok_set(all, e, T.Ent.k(e), T.Ent.p(e), oe), pt.rooted_mono_set(h <> r, all, e, rs))
        case EQ{}:
          pt.and_t(T.ok(T.set(all, e), T.Ent.k(e), T.Ent.p(e)), T.rooted.go(r, T.set(all, e)), pt.ok_set(all, e, T.Ent.k(e), T.Ent.p(e), oe), pt.rooted_mono_set(r, all, e, pt.and_r(T.ok(all, T.Ent.k(h), T.Ent.p(h)), T.rooted.go(r, all), rs)))
        case GT{}:
          +na = T.set(all, e)
          +oh = pt.and_l(T.ok(all, T.Ent.k(h), T.Ent.p(h)), T.rooted.go(r, all), rs)
          +rr = pt.and_r(T.ok(all, T.Ent.k(h), T.Ent.p(h)), T.rooted.go(r, all), rs)
          pt.and_t(T.ok(na, T.Ent.k(h), T.Ent.p(h)), T.rooted.go(T.set.go(r, e, T.first(T.Ent.k(e), r)), na), pt.ok_set(all, e, T.Ent.k(h), T.Ent.p(h), oh), pt.rooted_set_go(r, all, e, T.first(T.Ent.k(e), r), rr, oe))

def pt.put_sound(+t: List<&2, T.Ent>, +k: Nat, +p: Nat, +v: Nat, b: Bool, eb: {T.ok(t, k, p) == b : Bool}, +st: {T.sound(t) == True{} : Bool}) -> {T.sound(T.put.at(b, t, T.Ent{k, p, v})) == True{} : Bool}:
  match b:
    case True{}:
      +e = {T.Ent{k, p, v} : T.Ent}
      +s = T.set(t, e)
      pt.and_t(T.sorted(s), T.rooted(s), pt.sorted_set_go(t, e, T.first(k, t), {==}, pt.and_l(T.sorted(t), T.rooted(t), st)), pt.rooted_set_go(t, t, e, T.first(k, t), pt.and_r(T.sorted(t), T.rooted(t), st), eb))
    case False{}:
      st

# A delete
# --------

def pt.above_prune_go(t: List<&2, T.Ent>, +gone: List<&2, Nat>, hit: Bool, +l: Nat, al: {T.above(l, t) == True{} : Bool}, +st: {T.sorted(t) == True{} : Bool}) -> {T.above(l, T.prune.go(t, gone, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +g2 = {T.Ent.k(h) <> gone : List<&2, Nat>}
          pt.above_prune_go(r, g2, T.gone.at(r, g2), l, pt.above_tail(l, h, r, al, st), pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st))
        case False{}:
          al

def pt.sorted_prune_go(t: List<&2, T.Ent>, +gone: List<&2, Nat>, hit: Bool, +st: {T.sorted(t) == True{} : Bool}) -> {T.sorted(T.prune.go(t, gone, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +g2 = {T.Ent.k(h) <> gone : List<&2, Nat>}
          pt.sorted_prune_go(r, g2, T.gone.at(r, g2), pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st))
        case False{}:
          +sr = pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st)
          +u = T.prune.go(r, gone, T.gone.at(r, gone))
          pt.and_t(T.above(T.Ent.k(h), u), T.sorted(u), pt.above_prune_go(r, gone, T.gone.at(r, gone), T.Ent.k(h), pt.and_l(T.above(T.Ent.k(h), r), T.sorted(r), st), sr), pt.sorted_prune_go(r, gone, T.gone.at(r, gone), sr))

# every node of pre is kept in b, or its key is gone
def pt.cov(pre: List<&2, T.Ent>, +b: List<&2, T.Ent>, +gone: List<&2, Nat>) -> Bool:
  match pre:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Bool.or(T.has(b, T.Ent.k(e)), T.elem(gone, T.Ent.k(e))), pt.cov(rest, b, gone))

# every node of s hangs under the root, a node of pre, or a node before it
def pt.upl(s: List<&2, T.Ent>, +pre: List<&2, T.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(T.ok(pre, T.Ent.k(e), T.Ent.p(e)), pt.upl(rest, List.append(&2, T.Ent, pre, [e])))

def pt.cov_app(A: List<&2, T.Ent>, +C: List<&2, T.Ent>, +b: List<&2, T.Ent>, +g: List<&2, Nat>, +ca: {pt.cov(A, b, g) == True{} : Bool}, +cc: {pt.cov(C, b, g) == True{} : Bool}) -> {pt.cov(List.append(&2, T.Ent, A, C), b, g) == True{} : Bool}:
  match A:
    case Nil{}:
      cc
    case +a <> +r:
      +i = Bool.or(T.has(b, T.Ent.k(a)), T.elem(g, T.Ent.k(a)))
      pt.and_t(i, pt.cov(List.append(&2, T.Ent, r, C), b, g), pt.and_l(i, pt.cov(r, b, g), ca), pt.cov_app(r, C, b, g, pt.and_r(i, pt.cov(r, b, g), ca), cc))

def pt.or_mono_elem(c: Bool, +g: List<&2, Nat>, +y: Nat, +x: Nat, h: {Bool.or(c, T.elem(g, x)) == True{} : Bool}) -> {Bool.or(c, T.elem(y <> g, x)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pt.or_tr(Nat.is_eq(y, x), T.elem(g, x), h)

def pt.cov_gone(A: List<&2, T.Ent>, +b: List<&2, T.Ent>, +g: List<&2, Nat>, +y: Nat, +ca: {pt.cov(A, b, g) == True{} : Bool}) -> {pt.cov(A, b, y <> g) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +i = Bool.or(T.has(b, T.Ent.k(a)), T.elem(g, T.Ent.k(a)))
      pt.and_t(Bool.or(T.has(b, T.Ent.k(a)), T.elem(y <> g, T.Ent.k(a))), pt.cov(r, b, y <> g), pt.or_mono_elem(T.has(b, T.Ent.k(a)), g, y, T.Ent.k(a), pt.and_l(i, pt.cov(r, b, g), ca)), pt.cov_gone(r, b, g, y, pt.and_r(i, pt.cov(r, b, g), ca)))

def pt.or_mono_app(+b: List<&2, T.Ent>, +C: List<&2, T.Ent>, +g: List<&2, Nat>, +x: Nat, c: Bool, ec: {T.has(b, x) == c : Bool}, h: {Bool.or(c, T.elem(g, x)) == True{} : Bool}) -> {Bool.or(T.has(List.append(&2, T.Ent, b, C), x), T.elem(g, x)) == True{} : Bool}:
  match c:
    case True{}:
      pt.or_tl(T.has(List.append(&2, T.Ent, b, C), x), T.elem(g, x), pt.has_app_l(b, C, x, ec))
    case False{}:
      pt.or_tr(T.has(List.append(&2, T.Ent, b, C), x), T.elem(g, x), h)

def pt.cov_b(A: List<&2, T.Ent>, +b: List<&2, T.Ent>, +C: List<&2, T.Ent>, +g: List<&2, Nat>, +ca: {pt.cov(A, b, g) == True{} : Bool}) -> {pt.cov(A, List.append(&2, T.Ent, b, C), g) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +i = Bool.or(T.has(b, T.Ent.k(a)), T.elem(g, T.Ent.k(a)))
      pt.and_t(Bool.or(T.has(List.append(&2, T.Ent, b, C), T.Ent.k(a)), T.elem(g, T.Ent.k(a))), pt.cov(r, List.append(&2, T.Ent, b, C), g), pt.or_mono_app(b, C, g, T.Ent.k(a), T.has(b, T.Ent.k(a)), {==}, pt.and_l(i, pt.cov(r, b, g), ca)), pt.cov_b(r, b, C, g, pt.and_r(i, pt.cov(r, b, g), ca)))

def pt.cov_has_go(+e: T.Ent, +r: List<&2, T.Ent>, +b: List<&2, T.Ent>, +g: List<&2, Nat>, +y: Nat, c: Bool, ec: {Nat.is_eq(T.Ent.k(e), y) == c : Bool}, he: {Bool.or(T.has(b, T.Ent.k(e)), T.elem(g, T.Ent.k(e))) == True{} : Bool}, ih: {T.has(r, y) == True{} : Bool} -> {Bool.or(T.has(b, y), T.elem(g, y)) == True{} : Bool}, hp: {T.has(e <> r, y) == True{} : Bool}) -> {Bool.or(T.has(b, y), T.elem(g, y)) == True{} : Bool}:
  match c:
    case True{}:
      %pt.eq_true(T.Ent.k(e), y, ec) : {Bool.or(T.has(b, _), T.elem(g, _)) == True{} : Bool}
      he
    case False{}:
      ih(Equal.trans(Bool, T.has(r, y), T.has(e <> r, y), True{}, Equal.sym(Bool, T.has(e <> r, y), T.has(r, y), pt.has_miss(e, r, y, ec)), hp))

# a node of pre is kept or gone
def pt.cov_has(pre: List<&2, T.Ent>, +b: List<&2, T.Ent>, +g: List<&2, Nat>, +y: Nat, +cv: {pt.cov(pre, b, g) == True{} : Bool}) -> {T.has(pre, y) == True{} : Bool} -> {Bool.or(T.has(b, y), T.elem(g, y)) == True{} : Bool}:
  match pre:
    case Nil{}:
      hp => pt.absurdF({Bool.or(T.has(b, y), T.elem(g, y)) == True{} : Bool}, hp)
    case +e <> +r:
      +i = Bool.or(T.has(b, T.Ent.k(e)), T.elem(g, T.Ent.k(e)))
      +he = pt.and_l(i, pt.cov(r, b, g), cv)
      ih = pt.cov_has(r, b, g, y, pt.and_r(i, pt.cov(r, b, g), cv))
      hp => pt.cov_has_go(e, r, b, g, y, Nat.is_eq(T.Ent.k(e), y), {==}, he, ih, hp)

def pt.ok_keep_go(c: Bool, +pre: List<&2, T.Ent>, +b: List<&2, T.Ent>, +gone: List<&2, Nat>, +X: List<&2, T.Ent>, +p: Nat, o: {Bool.or(c, T.has(pre, p)) == True{} : Bool}, +cv: {pt.cov(pre, b, gone) == True{} : Bool}, ng: {T.elem(gone, p) == False{} : Bool}) -> {Bool.or(c, T.has(List.append(&2, T.Ent, b, X), p)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +q = pt.cov_has(pre, b, gone, p, cv)(o)
      pt.has_app_l(b, X, p, pt.or_l_true(T.has(b, p), T.elem(gone, p), q, ng))

# a kept node still hangs under the root or a kept node
def pt.ok_keep(+pre: List<&2, T.Ent>, +b: List<&2, T.Ent>, +gone: List<&2, Nat>, +X: List<&2, T.Ent>, +k: Nat, +p: Nat, +op: {T.ok(pre, k, p) == True{} : Bool}, +cv: {pt.cov(pre, b, gone) == True{} : Bool}, ng: {T.elem(gone, p) == False{} : Bool}) -> {T.ok(List.append(&2, T.Ent, b, X), k, p) == True{} : Bool}:
  +o = pt.and_r(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), T.has(pre, p)), op)
  pt.and_t(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), T.has(List.append(&2, T.Ent, b, X), p)), pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), T.has(pre, p)), op), pt.ok_keep_go(Nat.is_eq(p, 0n), pre, b, gone, X, p, o, cv, ng))

def pt.upl_of(s: List<&2, T.Ent>, +pre: List<&2, T.Ent>, +rs: {T.rooted.go(s, List.append(&2, T.Ent, pre, s)) == True{} : Bool}, +st: {T.sorted(List.append(&2, T.Ent, pre, s)) == True{} : Bool}) -> {pt.upl(s, pre) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +k = T.Ent.k(e)
      +p = T.Ent.p(e)
      +X = {e <> r : List<&2, T.Ent>}
      +A = List.append(&2, T.Ent, pre, X)
      +pre2 = List.append(&2, T.Ent, pre, [e])
      +oA = pt.and_l(T.ok(A, k, p), T.rooted.go(r, A), rs)
      +lt = pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), T.has(A, p)), oA)
      +hx = pt.has_below(X, p, lt, pt.sorted_app_r(pre, X, st))
      +hp = Equal.trans(Bool, T.has(A, p), Bool.or(T.has(pre, p), T.has(X, p)), T.has(pre, p), pt.has_app(pre, X, p), Equal.trans(Bool, Bool.or(T.has(pre, p), T.has(X, p)), Bool.or(T.has(pre, p), False{}), T.has(pre, p), Equal.cong(Bool, Bool, z => Bool.or(T.has(pre, p), z), T.has(X, p), False{}, hx), pt.or_false_r(T.has(pre, p))))
      +okp = Equal.trans(Bool, T.ok(pre, k, p), T.ok(A, k, p), True{}, Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), z)), T.has(pre, p), T.has(A, p), Equal.sym(Bool, T.has(A, p), T.has(pre, p), hp)), oA)
      +eq = pt.app_snoc(pre, e, r)
      +rs2 = Equal.trans(Bool, T.rooted.go(r, List.append(&2, T.Ent, pre2, r)), T.rooted.go(r, A), True{}, Equal.cong(List<&2, T.Ent>, Bool, l => T.rooted.go(r, l), List.append(&2, T.Ent, pre2, r), A, eq), pt.and_r(T.ok(A, k, p), T.rooted.go(r, A), rs))
      +st2 = Equal.trans(Bool, T.sorted(List.append(&2, T.Ent, pre2, r)), T.sorted(A), True{}, Equal.cong(List<&2, T.Ent>, Bool, l => T.sorted(l), List.append(&2, T.Ent, pre2, r), A, eq), st)
      pt.and_t(T.ok(pre, k, p), pt.upl(r, pre2), okp, pt.upl_of(r, pre2, rs2, st2))

# the nodes prune keeps hang under the root or under kept nodes
def pt.rooted_prune_go(s: List<&2, T.Ent>, +gone: List<&2, Nat>, hit: Bool, eh: {T.gone.at(s, gone) == hit : Bool}, +pre: List<&2, T.Ent>, +b: List<&2, T.Ent>, +cv: {pt.cov(pre, b, gone) == True{} : Bool}, +up: {pt.upl(s, pre) == True{} : Bool}) -> {T.rooted.go(T.prune.go(s, gone, hit), List.append(&2, T.Ent, b, T.prune.go(s, gone, hit))) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +k = T.Ent.k(e)
          +g2 = {k <> gone : List<&2, Nat>}
          +pre2 = List.append(&2, T.Ent, pre, [e])
          +c1 = pt.and_t(Bool.or(T.has(b, k), T.elem(g2, k)), True{}, pt.or_tr(T.has(b, k), T.elem(g2, k), pt.or_tl(Nat.is_eq(k, k), T.elem(gone, k), Equal.sym(Bool, True{}, Nat.is_eq(k, k), pt.eq_refl(k)))), {==})
          +cv2 = pt.cov_app(pre, [e], b, g2, pt.cov_gone(pre, b, gone, k, cv), c1)
          pt.rooted_prune_go(r, g2, T.gone.at(r, g2), {==}, pre2, b, cv2, pt.and_r(T.ok(pre, k, T.Ent.p(e)), pt.upl(r, pre2), up))
        case False{}:
          +k = T.Ent.k(e)
          +p = T.Ent.p(e)
          +P = T.prune.go(r, gone, T.gone.at(r, gone))
          +pre2 = List.append(&2, T.Ent, pre, [e])
          +b2 = List.append(&2, T.Ent, b, [e])
          +ng = pt.or_r(T.elem(gone, k), T.elem(gone, p), eh)
          +ok1 = pt.ok_keep(pre, b, gone, e <> P, k, p, pt.and_l(T.ok(pre, k, p), pt.upl(r, pre2), up), cv, ng)
          +c2 = pt.and_t(Bool.or(T.has(b2, k), T.elem(gone, k)), True{}, pt.or_tl(T.has(b2, k), T.elem(gone, k), pt.has_app_r(b, [e], k, pt.has_head(e, Nil{}))), {==})
          +cv2 = pt.cov_app(pre, [e], b2, gone, pt.cov_b(pre, b, [e], gone, cv), c2)
          +ih = pt.rooted_prune_go(r, gone, T.gone.at(r, gone), {==}, pre2, b2, cv2, pt.and_r(T.ok(pre, k, p), pt.upl(r, pre2), up))
          +eq = pt.app_snoc(b, e, P)
          +rest = Equal.trans(Bool, T.rooted.go(P, List.append(&2, T.Ent, b, e <> P)), T.rooted.go(P, List.append(&2, T.Ent, b2, P)), True{}, Equal.cong(List<&2, T.Ent>, Bool, l => T.rooted.go(P, l), List.append(&2, T.Ent, b, e <> P), List.append(&2, T.Ent, b2, P), Equal.sym(List<&2, T.Ent>, List.append(&2, T.Ent, b2, P), List.append(&2, T.Ent, b, e <> P), eq)), ih)
          pt.and_t(T.ok(List.append(&2, T.Ent, b, e <> P), k, p), T.rooted.go(P, List.append(&2, T.Ent, b, e <> P)), ok1, rest)

def pt.del_sound(+t: List<&2, T.Ent>, +x: Nat, +st: {T.sound(t) == True{} : Bool}) -> {T.sound(T.prune(t, x)) == True{} : Bool}:
  +R = T.prune(t, x)
  +so = pt.and_l(T.sorted(t), T.rooted(t), st)
  +ro = pt.and_r(T.sorted(t), T.rooted(t), st)
  pt.and_t(T.sorted(R), T.rooted(R), pt.sorted_prune_go(t, [x], T.gone.at(t, [x]), so), pt.rooted_prune_go(t, [x], T.gone.at(t, [x]), {==}, Nil{}, Nil{}, {==}, pt.upl_of(t, Nil{}, ro, so)))

def pt.keep_sound(+t: List<&2, T.Ent>, +n: List<&2, T.Ent>, b: Bool, eb: {T.sound(n) == b : Bool}, st: {T.sound(t) == True{} : Bool}) -> {T.sound(T.keep.at(b, t, n)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      st

# The journal
# -----------

def apply_sound(+t: List<&2, T.Ent>, +good: {T.sound(t) == True{} : Bool}, r: T.Rec) -> {T.sound(T.apply(t, r)) == True{} : Bool}:
  match r:
    case T.Do{o}:
      match o:
        case T.Put{+k, +p, +v}:
          pt.put_sound(t, k, p, v, T.ok(t, k, p), {==}, good)
        case T.Del{+x}:
          match x:
            case 0n:
              good
            case 1n+y:
              pt.del_sound(t, 1n+y, good)
    case T.Rewind{+ops}:
      pt.keep_sound(t, T.patch(ops, t), T.sound(T.patch(ops, t)), {==}, good)

def pt.go_sound(rs: List<&2, T.Rec>, +t: List<&2, T.Ent>, +st: {T.sound(t) == True{} : Bool}) -> {T.sound(T.go(rs, t)) == True{} : Bool}:
  match rs:
    case Nil{}:
      st
    case +r <> rest:
      pt.go_sound(rest, T.apply(t, r), apply_sound(t, st, r))

def replay_sound(+rs: List<&2, T.Rec>) -> {T.sound(T.replay(rs)) == True{} : Bool}:
  pt.go_sound(rs, Nil{}, {==})

def pt.go_append(pre: List<&2, T.Rec>, +post: List<&2, T.Rec>, +t: List<&2, T.Ent>) -> {T.go(post, T.go(pre, t)) == T.go(List.append(&2, T.Rec, pre, post), t) : List<&2, T.Ent>}:
  match pre:
    case Nil{}:
      {==}
    case +r <> rest:
      pt.go_append(rest, post, T.apply(t, r))

def snapshot(+pre: List<&2, T.Rec>, +post: List<&2, T.Rec>) -> {T.go(post, T.replay(pre)) == T.replay(List.append(&2, T.Rec, pre, post)) : List<&2, T.Ent>}:
  pt.go_append(pre, post, Nil{})

# A put
# -----

def put_sets(+t: List<&2, T.Ent>, good: {T.sound(t) == True{} : Bool}, +k: Nat, +p: Nat, +v: Nat, fits: {T.ok(t, k, p) == True{} : Bool}) -> {T.get(T.apply(t, T.Do{T.Put{k, p, v}}), k) == Some{T.Ent{k, p, v}} : Maybe<&2, T.Ent>}:
  %Equal.sym(Bool, T.ok(t, k, p), True{}, fits) : {T.get(T.put.at(_, t, T.Ent{k, p, v}), k) == Some{T.Ent{k, p, v}} : Maybe<&2, T.Ent>}
  pt.get_set_same(t, T.Ent{k, p, v})

def pt.put_at_other(+t: List<&2, T.Ent>, +k: Nat, +p: Nat, +v: Nat, +x: Nat, b: Bool, ne: {Nat.is_eq(k, x) == False{} : Bool}) -> {T.get(T.put.at(b, t, T.Ent{k, p, v}), x) == T.get(t, x) : Maybe<&2, T.Ent>}:
  match b:
    case True{}:
      pt.get_set_other(t, T.Ent{k, p, v}, x, ne)
    case False{}:
      {==}

def put_keeps_others(+t: List<&2, T.Ent>, good: {T.sound(t) == True{} : Bool}, +k: Nat, +p: Nat, +v: Nat, +x: Nat, other: {Nat.is_eq(x, k) == False{} : Bool}) -> {T.get(T.apply(t, T.Do{T.Put{k, p, v}}), x) == T.get(t, x) : Maybe<&2, T.Ent>}:
  pt.put_at_other(t, k, p, v, x, T.ok(t, k, p), pt.ne_comm(x, k, other))

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
  pt.ne_comm(x, a, pt.ne_by(x, a, f, nx, ha))

def pt.eq_of(+a: Nat, +b: Nat, ab: {a == b : Nat}) -> {Nat.is_eq(b, a) == True{} : Bool}:
  %ab : {Nat.is_eq(_, a) == True{} : Bool}
  Equal.sym(Bool, True{}, Nat.is_eq(a, a), pt.eq_refl(a))

def pt.val(m: Maybe<&2, T.Ent>, d: T.Ent) -> T.Ent:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def pt.some_inj(+x: T.Ent, +y: T.Ent, h: {Some{x} == Some{y} : Maybe<&2, T.Ent>}) -> {x == y : T.Ent}:
  Equal.cong(Maybe<&2, T.Ent>, T.Ent, m => pt.val(m, x), Some{x}, Some{y}, h)

def pt.get_below(X: List<&2, T.Ent>, +y: Nat, +al: {T.above(y, X) == True{} : Bool}, +st: {T.sorted(X) == True{} : Bool}) -> {T.get(X, y) == None{} : Maybe<&2, T.Ent>}:
  match X:
    case Nil{}:
      {==}
    case +h <> +r:
      Equal.trans(Maybe<&2, T.Ent>, T.get(h <> r, y), T.get(r, y), None{}, pt.get_miss(h, r, y, pt.lt_ne_r(y, T.Ent.k(h), al)), pt.get_below(r, y, pt.above_tail(y, h, r, al, st), pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st)))

# Delete: removes, within
# -----------------------

def pt.removes_go(s: List<&2, T.Ent>, +gone: List<&2, Nat>, hit: Bool, eh: {T.gone.at(s, gone) == hit : Bool}, +x: Nat, +ex: {T.elem(gone, x) == True{} : Bool}) -> {T.has(T.prune.go(s, gone, hit), x) == False{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +g2 = {T.Ent.k(e) <> gone : List<&2, Nat>}
          pt.removes_go(r, g2, T.gone.at(r, g2), {==}, x, pt.or_tr(Nat.is_eq(T.Ent.k(e), x), T.elem(gone, x), ex))
        case False{}:
          +P = T.prune.go(r, gone, T.gone.at(r, gone))
          +ng = pt.or_l(T.elem(gone, T.Ent.k(e)), T.elem(gone, T.Ent.p(e)), eh)
          +ne = pt.ne_by(T.Ent.k(e), x, z => T.elem(gone, z), ng, ex)
          Equal.trans(Bool, T.has(e <> P, x), T.has(P, x), False{}, pt.has_miss(e, P, x, ne), pt.removes_go(r, gone, T.gone.at(r, gone), {==}, x, ex))

def pt.removes_nz(+t: List<&2, T.Ent>, +x: Nat) -> {T.has(T.prune(t, x), x) == False{} : Bool}:
  pt.removes_go(t, [x], T.gone.at(t, [x]), {==}, x, pt.or_tl(Nat.is_eq(x, x), False{}, Equal.sym(Bool, True{}, Nat.is_eq(x, x), pt.eq_refl(x))))

# a key above a parent is not the root
def pt.key_nz(p: Nat, k: Nat, lt: {Nat.is_lt(p, k) == True{} : Bool}) -> {Nat.is_eq(k, 0n) == False{} : Bool}:
  match p k:
    case 0n 0n:
      pt.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, lt)
    case 1n+q 0n:
      pt.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, lt)
    case _ 1n+q:
      {==}

# no node of a rooted list is the root
def pt.rooted_nz(s: List<&2, T.Ent>, +all: List<&2, T.Ent>, +rs: {T.rooted.go(s, all) == True{} : Bool}) -> {T.has(s, 0n) == False{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +k = T.Ent.k(e)
      +p = T.Ent.p(e)
      +oe = pt.and_l(T.ok(all, k, p), T.rooted.go(r, all), rs)
      +lt = pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), T.has(all, p)), oe)
      Equal.trans(Bool, T.has(e <> r, 0n), T.has(r, 0n), False{}, pt.has_miss(e, r, 0n, pt.key_nz(p, k, lt)), pt.rooted_nz(r, all, pt.and_r(T.ok(all, k, p), T.rooted.go(r, all), rs)))

# a delete of the root changes nothing, and the root is no node
def delete_removes(+t: List<&2, T.Ent>, +good: {T.sound(t) == True{} : Bool}, +x: Nat) -> {T.has(T.apply(t, T.Do{T.Del{x}}), x) == False{} : Bool}:
  match x:
    case 0n:
      pt.rooted_nz(t, t, pt.and_r(T.sorted(t), T.rooted(t), good))
    case 1n+y:
      pt.removes_nz(t, 1n+y)

def pt.within_prune_go(s: List<&2, T.Ent>, +gone: List<&2, Nat>, hit: Bool, +t: List<&2, T.Ent>, +w: {T.within(s, t) == True{} : Bool}) -> {T.within(T.prune.go(s, gone, hit), t) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = T.same(T.get(t, T.Ent.k(e)), Some{e})
          +g2 = {T.Ent.k(e) <> gone : List<&2, Nat>}
          pt.within_prune_go(r, g2, T.gone.at(r, g2), t, pt.and_r(i, T.within(r, t), w))
        case False{}:
          +i = T.same(T.get(t, T.Ent.k(e)), Some{e})
          +P = T.prune.go(r, gone, T.gone.at(r, gone))
          pt.and_t(i, T.within(P, t), pt.and_l(i, T.within(r, t), w), pt.within_prune_go(r, gone, T.gone.at(r, gone), t, pt.and_r(i, T.within(r, t), w)))

# a node above every node of s does not change what s holds
def pt.within_cons(s: List<&2, T.Ent>, +h: T.Ent, +r: List<&2, T.Ent>, +w: {T.within(s, r) == True{} : Bool}, +al: {T.above(T.Ent.k(h), s) == True{} : Bool}, +st: {T.sorted(s) == True{} : Bool}) -> {T.within(s, h <> r) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +i = T.same(T.get(r, T.Ent.k(e)), Some{e})
      +gm = pt.get_miss(h, r, T.Ent.k(e), pt.lt_ne(T.Ent.k(h), T.Ent.k(e), al))
      +hd = Equal.trans(Bool, T.same(T.get(h <> r, T.Ent.k(e)), Some{e}), i, True{}, Equal.cong(Maybe<&2, T.Ent>, Bool, m => T.same(m, Some{e}), T.get(h <> r, T.Ent.k(e)), T.get(r, T.Ent.k(e)), gm), pt.and_l(i, T.within(rest, r), w))
      pt.and_t(T.same(T.get(h <> r, T.Ent.k(e)), Some{e}), T.within(rest, h <> r), hd, pt.within_cons(rest, h, r, pt.and_r(i, T.within(rest, r), w), pt.above_tail(T.Ent.k(h), e, rest, al, st), pt.and_r(T.above(T.Ent.k(e), rest), T.sorted(rest), st)))

# a sorted tree holds each of its nodes
def pt.within_self(t: List<&2, T.Ent>, +st: {T.sorted(t) == True{} : Bool}) -> {T.within(t, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      +sr = pt.and_r(T.above(T.Ent.k(h), r), T.sorted(r), st)
      +hd = Equal.trans(Bool, T.same(T.get(h <> r, T.Ent.k(h)), Some{h}), T.same(Some{h}, Some{h}), True{}, Equal.cong(Maybe<&2, T.Ent>, Bool, m => T.same(m, Some{h}), T.get(h <> r, T.Ent.k(h)), Some{h}, pt.get_head(h, r)), pt.same_refl(h))
      pt.and_t(T.same(T.get(h <> r, T.Ent.k(h)), Some{h}), T.within(r, h <> r), hd, pt.within_cons(r, h, r, pt.within_self(r, sr), pt.and_l(T.above(T.Ent.k(h), r), T.sorted(r), st), sr))

def delete_within(+t: List<&2, T.Ent>, +good: {T.sound(t) == True{} : Bool}, +x: Nat) -> {T.within(T.apply(t, T.Do{T.Del{x}}), t) == True{} : Bool}:
  match x:
    case 0n:
      pt.within_self(t, pt.and_l(T.sorted(t), T.rooted(t), good))
    case 1n+y:
      pt.within_prune_go(t, [1n+y], T.gone.at(t, [1n+y]), t, pt.within_self(t, pt.and_l(T.sorted(t), T.rooted(t), good)))

# Rewind: still, minimal
# ----------------------

# b has the key of every node of s
def pt.allhas(s: List<&2, T.Ent>, +b: List<&2, T.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(T.has(b, T.Ent.k(e)), pt.allhas(rest, b))

def pt.allhas_cons(s: List<&2, T.Ent>, +h: T.Ent, +r: List<&2, T.Ent>, +ah: {pt.allhas(s, r) == True{} : Bool}) -> {pt.allhas(s, h <> r) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +i = T.has(r, T.Ent.k(e))
      +hd = Equal.trans(Bool, T.has(h <> r, T.Ent.k(e)), Bool.or(Nat.is_eq(T.Ent.k(h), T.Ent.k(e)), i), True{}, pt.has_cons(h, r, T.Ent.k(e)), pt.or_tr(Nat.is_eq(T.Ent.k(h), T.Ent.k(e)), i, pt.and_l(i, pt.allhas(rest, r), ah)))
      pt.and_t(T.has(h <> r, T.Ent.k(e)), pt.allhas(rest, h <> r), hd, pt.allhas_cons(rest, h, r, pt.and_r(i, pt.allhas(rest, r), ah)))

def pt.allhas_self(t: List<&2, T.Ent>) -> {pt.allhas(t, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      pt.and_t(T.has(h <> r, T.Ent.k(h)), pt.allhas(r, h <> r), pt.has_head(h, r), pt.allhas_cons(r, h, r, pt.allhas_self(r)))

def pt.dels_nil(s: List<&2, T.Ent>, +b: List<&2, T.Ent>, hit: Bool, eh: {T.held.at(s, b) == hit : Bool}, +ah: {pt.allhas(s, b) == True{} : Bool}) -> {T.dels.go(s, b, hit) == Nil{} : List<&2, T.Op>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = T.has(b, T.Ent.k(e))
          pt.dels_nil(r, b, T.held.at(r, b), {==}, pt.and_r(i, pt.allhas(r, b), ah))
        case False{}:
          +i = T.has(b, T.Ent.k(e))
          pt.void({T.dels.go(e <> r, b, False{}) == Nil{} : List<&2, T.Op>}, pt.flip(i, pt.and_l(i, pt.allhas(r, b), ah), eh))

def pt.puts_nil(+a: List<&2, T.Ent>, s: List<&2, T.Ent>, hit: Bool, eh: {T.kept.at(a, s) == hit : Bool}, +w: {T.within(s, a) == True{} : Bool}) -> {T.puts.go(a, s, hit) == Nil{} : List<&2, T.Op>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = T.same(T.get(a, T.Ent.k(e)), Some{e})
          pt.puts_nil(a, r, T.kept.at(a, r), {==}, pt.and_r(i, T.within(r, a), w))
        case False{}:
          +i = T.same(T.get(a, T.Ent.k(e)), Some{e})
          pt.void({T.puts.go(a, e <> r, False{}) == Nil{} : List<&2, T.Op>}, pt.flip(i, pt.and_l(i, T.within(r, a), w), eh))

def rewind_still(+a: List<&2, T.Ent>, ga: {T.sorted(a) == True{} : Bool}) -> {T.diff(a, a) == Nil{} : List<&2, T.Op>}:
  %Equal.sym(List<&2, T.Op>, T.dels(a, a), Nil{}, pt.dels_nil(a, a, T.held.at(a, a), {==}, pt.allhas_self(a))) : {List.append(&2, T.Op, _, T.puts(a, a)) == Nil{} : List<&2, T.Op>}
  pt.puts_nil(a, a, T.kept.at(a, a), {==}, pt.within_self(a, ga))

def pt.changed_app(xs: List<&2, T.Op>, +ys: List<&2, T.Op>, +a: List<&2, T.Ent>, +b: List<&2, T.Ent>, +cx: {T.changed(a, b, xs) == True{} : Bool}, cy: {T.changed(a, b, ys) == True{} : Bool}) -> {T.changed(a, b, List.append(&2, T.Op, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      cy
    case +o <> +r:
      +i = Bool.not(T.same(T.get(a, T.Op.k(o)), T.get(b, T.Op.k(o))))
      pt.and_t(i, T.changed(a, b, List.append(&2, T.Op, r, ys)), pt.and_l(i, T.changed(a, b, r), cx), pt.changed_app(r, ys, a, b, pt.and_r(i, T.changed(a, b, r), cx), cy))

# a node one side holds and the other lacks differs
def pt.same_has(m1: Maybe<&2, T.Ent>, m2: Maybe<&2, T.Ent>, h1: {Maybe.is_some(&2, T.Ent, m1) == True{} : Bool}, h2: {Maybe.is_some(&2, T.Ent, m2) == False{} : Bool}) -> {Bool.not(T.same(m1, m2)) == True{} : Bool}:
  match m1 m2:
    case None{} _:
      pt.absurdF({Bool.not(T.same(None{}, m2)) == True{} : Bool}, h1)
    case Some{x} None{}:
      {==}
    case Some{x} Some{y}:
      pt.absurd({Bool.not(T.same(Some{x}, Some{y})) == True{} : Bool}, h2)

def pt.dels_changed(s: List<&2, T.Ent>, +a: List<&2, T.Ent>, +b: List<&2, T.Ent>, hit: Bool, eh: {T.held.at(s, b) == hit : Bool}, +ah: {pt.allhas(s, a) == True{} : Bool}) -> {T.changed(a, b, T.dels.go(s, b, hit)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = T.has(a, T.Ent.k(e))
          pt.dels_changed(r, a, b, T.held.at(r, b), {==}, pt.and_r(i, pt.allhas(r, a), ah))
        case False{}:
          +i = T.has(a, T.Ent.k(e))
          +k = T.Ent.k(e)
          +d = Bool.not(T.same(T.get(a, k), T.get(b, k)))
          pt.and_t(d, T.changed(a, b, T.dels.go(r, b, T.held.at(r, b))), pt.same_has(T.get(a, k), T.get(b, k), pt.and_l(i, pt.allhas(r, a), ah), eh), pt.dels_changed(r, a, b, T.held.at(r, b), {==}, pt.and_r(i, pt.allhas(r, a), ah)))

def pt.put_differs(+a: List<&2, T.Ent>, +b: List<&2, T.Ent>, +e: T.Ent, eh: {T.same(T.get(a, T.Ent.k(e)), Some{e}) == False{} : Bool}, wb: {T.same(T.get(b, T.Ent.k(e)), Some{e}) == True{} : Bool}) -> {Bool.not(T.same(T.get(a, T.Ent.k(e)), T.get(b, T.Ent.k(e)))) == True{} : Bool}:
  %Equal.sym(Maybe<&2, T.Ent>, T.get(b, T.Ent.k(e)), Some{e}, pt.same_some(T.get(b, T.Ent.k(e)), e, wb)) : {Bool.not(T.same(T.get(a, T.Ent.k(e)), _)) == True{} : Bool}
  %Equal.sym(Bool, T.same(T.get(a, T.Ent.k(e)), Some{e}), False{}, eh) : {Bool.not(_) == True{} : Bool}
  {==}

def pt.puts_changed(+a: List<&2, T.Ent>, s: List<&2, T.Ent>, +b: List<&2, T.Ent>, hit: Bool, eh: {T.kept.at(a, s) == hit : Bool}, +w: {T.within(s, b) == True{} : Bool}) -> {T.changed(a, b, T.puts.go(a, s, hit)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = T.same(T.get(b, T.Ent.k(e)), Some{e})
          pt.puts_changed(a, r, b, T.kept.at(a, r), {==}, pt.and_r(i, T.within(r, b), w))
        case False{}:
          +i = T.same(T.get(b, T.Ent.k(e)), Some{e})
          +k = T.Ent.k(e)
          +d = Bool.not(T.same(T.get(a, k), T.get(b, k)))
          pt.and_t(d, T.changed(a, b, T.puts.go(a, r, T.kept.at(a, r))), pt.put_differs(a, b, e, eh, pt.and_l(i, T.within(r, b), w)), pt.puts_changed(a, r, b, T.kept.at(a, r), {==}, pt.and_r(i, T.within(r, b), w)))

def rewind_minimal(+a: List<&2, T.Ent>, +b: List<&2, T.Ent>, ga: {T.sorted(a) == True{} : Bool}, gb: {T.sorted(b) == True{} : Bool}) -> {T.changed(a, b, T.diff(a, b)) == True{} : Bool}:
  pt.changed_app(T.dels(a, b), T.puts(a, b), a, b, pt.dels_changed(a, a, b, T.held.at(a, b), {==}, pt.allhas_self(a)), pt.puts_changed(a, b, b, T.kept.at(a, b), {==}, pt.within_self(b, gb)))

# Rewind: reaches
# ---------------
# A lookup after a patch follows the ops on its key (`pt.look`); the dels
# drop exactly the keys b lacks, the puts set exactly the nodes a lacks or
# holds differently. So the patched tree and b agree on every key, and two
# sorted trees that agree on their keys are equal (`pt.ext`).

def pt.pick(c: Bool, n: Maybe<&2, T.Ent>, m: Maybe<&2, T.Ent>) -> Maybe<&2, T.Ent>:
  match c:
    case True{}:
      n
    case False{}:
      m

# the node at key x after one op, from m
def pt.upd(o: T.Op, m: Maybe<&2, T.Ent>, +x: Nat) -> Maybe<&2, T.Ent>:
  match o:
    case T.Put{+k, p, v}:
      pt.pick(Nat.is_eq(k, x), Some{T.Ent{k, p, v}}, m)
    case T.Del{k}:
      pt.pick(Nat.is_eq(k, x), None{}, m)

# the node at key x after the ops, from m
def pt.look(ops: List<&2, T.Op>, m: Maybe<&2, T.Ent>, +x: Nat) -> Maybe<&2, T.Ent>:
  match ops:
    case Nil{}:
      m
    case o <> rest:
      pt.look(rest, pt.upd(o, m, x), x)

def pt.get_put_go(+t: List<&2, T.Ent>, +k: Nat, +p: Nat, +v: Nat, +x: Nat, c: Bool, ec: {Nat.is_eq(k, x) == c : Bool}) -> {T.get(T.set(t, T.Ent{k, p, v}), x) == pt.pick(c, Some{T.Ent{k, p, v}}, T.get(t, x)) : Maybe<&2, T.Ent>}:
  match c:
    case True{}:
      %pt.eq_true(k, x, ec) : {T.get(T.set(t, T.Ent{k, p, v}), _) == Some{T.Ent{k, p, v}} : Maybe<&2, T.Ent>}
      pt.get_set_same(t, T.Ent{k, p, v})
    case False{}:
      pt.get_set_other(t, T.Ent{k, p, v}, x, ec)

def pt.get_del_go(+t: List<&2, T.Ent>, +y: Nat, +x: Nat, c: Bool, ec: {Nat.is_eq(y, x) == c : Bool}) -> {T.get(T.unset(t, y), x) == pt.pick(c, None{}, T.get(t, x)) : Maybe<&2, T.Ent>}:
  match c:
    case True{}:
      %pt.eq_true(y, x, ec) : {T.get(T.unset(t, y), _) == None{} : Maybe<&2, T.Ent>}
      pt.get_unset_same(t, y)
    case False{}:
      pt.get_unset_other(t, y, x, ec)

def pt.get_exact(+t: List<&2, T.Ent>, o: T.Op, +x: Nat) -> {T.get(T.exact(t, o), x) == pt.upd(o, T.get(t, x), x) : Maybe<&2, T.Ent>}:
  match o:
    case T.Put{+k, +p, +v}:
      pt.get_put_go(t, k, p, v, x, Nat.is_eq(k, x), {==})
    case T.Del{+y}:
      pt.get_del_go(t, y, x, Nat.is_eq(y, x), {==})

def pt.get_patch(ops: List<&2, T.Op>, +t: List<&2, T.Ent>, +x: Nat) -> {T.get(T.patch(ops, t), x) == pt.look(ops, T.get(t, x), x) : Maybe<&2, T.Ent>}:
  match ops:
    case Nil{}:
      {==}
    case +o <> +rest:
      +t2 = T.exact(t, o)
      Equal.trans(Maybe<&2, T.Ent>, T.get(T.patch(rest, t2), x), pt.look(rest, T.get(t2, x), x), pt.look(rest, pt.upd(o, T.get(t, x), x), x), pt.get_patch(rest, t2, x), Equal.cong(Maybe<&2, T.Ent>, Maybe<&2, T.Ent>, m => pt.look(rest, m, x), T.get(t2, x), pt.upd(o, T.get(t, x), x), pt.get_exact(t, o, x)))

def pt.look_app(xs: List<&2, T.Op>, +ys: List<&2, T.Op>, +m: Maybe<&2, T.Ent>, +x: Nat) -> {pt.look(List.append(&2, T.Op, xs, ys), m, x) == pt.look(ys, pt.look(xs, m, x), x) : Maybe<&2, T.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +r:
      pt.look_app(r, ys, pt.upd(o, m, x), x)

def pt.pick_same(c: Bool, +m: Maybe<&2, T.Ent>) -> {pt.pick(c, m, m) == m : Maybe<&2, T.Ent>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def pt.dels_none(s: List<&2, T.Ent>, +b: List<&2, T.Ent>, hit: Bool, +x: Nat) -> {pt.look(T.dels.go(s, b, hit), None{}, x) == None{} : Maybe<&2, T.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          pt.dels_none(r, b, T.held.at(r, b), x)
        case False{}:
          +c = Nat.is_eq(T.Ent.k(e), x)
          %Equal.sym(Maybe<&2, T.Ent>, pt.pick(c, None{}, None{}), None{}, pt.pick_same(c, None{})) : {pt.look(T.dels.go(r, b, T.held.at(r, b)), _, x) == None{} : Maybe<&2, T.Ent>}
          pt.dels_none(r, b, T.held.at(r, b), x)

# the dels leave a key the target holds
def pt.dels_keep(s: List<&2, T.Ent>, +b: List<&2, T.Ent>, hit: Bool, eh: {T.held.at(s, b) == hit : Bool}, +m: Maybe<&2, T.Ent>, +x: Nat, +hb: {T.has(b, x) == True{} : Bool}) -> {pt.look(T.dels.go(s, b, hit), m, x) == m : Maybe<&2, T.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          pt.dels_keep(r, b, T.held.at(r, b), {==}, m, x, hb)
        case False{}:
          +ne = pt.ne_by(T.Ent.k(e), x, z => T.has(b, z), eh, hb)
          %Equal.sym(Bool, Nat.is_eq(T.Ent.k(e), x), False{}, ne) : {pt.look(T.dels.go(r, b, T.held.at(r, b)), pt.pick(_, None{}, m), x) == m : Maybe<&2, T.Ent>}
          pt.dels_keep(r, b, T.held.at(r, b), {==}, m, x, hb)

def pt.dd_go(+e: T.Ent, +r: List<&2, T.Ent>, +b: List<&2, T.Ent>, +x: Nat, c: Bool, ec: {Nat.is_eq(T.Ent.k(e), x) == c : Bool}, ih: {pt.look(T.dels.go(r, b, T.held.at(r, b)), T.get(r, x), x) == None{} : Maybe<&2, T.Ent>}) -> {pt.look(T.dels.go(r, b, T.held.at(r, b)), pt.pick(c, None{}, T.get(e <> r, x)), x) == None{} : Maybe<&2, T.Ent>}:
  match c:
    case True{}:
      pt.dels_none(r, b, T.held.at(r, b), x)
    case False{}:
      %Equal.sym(Maybe<&2, T.Ent>, T.get(e <> r, x), T.get(r, x), pt.get_miss(e, r, x, ec)) : {pt.look(T.dels.go(r, b, T.held.at(r, b)), _, x) == None{} : Maybe<&2, T.Ent>}
      ih

# the dels drop a key the target lacks
def pt.dels_drop(s: List<&2, T.Ent>, +b: List<&2, T.Ent>, hit: Bool, eh: {T.held.at(s, b) == hit : Bool}, +x: Nat, +hb: {T.has(b, x) == False{} : Bool}) -> {pt.look(T.dels.go(s, b, hit), T.get(s, x), x) == None{} : Maybe<&2, T.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ne = pt.ne_by2(T.Ent.k(e), x, z => T.has(b, z), eh, hb)
          %Equal.sym(Maybe<&2, T.Ent>, T.get(e <> r, x), T.get(r, x), pt.get_miss(e, r, x, ne)) : {pt.look(T.dels.go(r, b, T.held.at(r, b)), _, x) == None{} : Maybe<&2, T.Ent>}
          pt.dels_drop(r, b, T.held.at(r, b), {==}, x, hb)
        case False{}:
          pt.dd_go(e, r, b, x, Nat.is_eq(T.Ent.k(e), x), {==}, pt.dels_drop(r, b, T.held.at(r, b), {==}, x, hb))

def pt.gnh_go(+e: T.Ent, +r: List<&2, T.Ent>, +x: Nat, c: Bool, ec: {Nat.is_eq(T.Ent.k(e), x) == c : Bool}, gn: {T.get(e <> r, x) == None{} : Maybe<&2, T.Ent>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      pt.some_none({True{} == False{} : Bool}, e, Equal.trans(Maybe<&2, T.Ent>, Some{e}, T.get(e <> r, x), None{}, Equal.sym(Maybe<&2, T.Ent>, T.get(e <> r, x), Some{e}, pt.get_hit(e, r, x, ec)), gn))
    case False{}:
      {==}

def pt.get_none_head(+e: T.Ent, +r: List<&2, T.Ent>, +x: Nat, gn: {T.get(e <> r, x) == None{} : Maybe<&2, T.Ent>}) -> {Nat.is_eq(T.Ent.k(e), x) == False{} : Bool}:
  pt.gnh_go(e, r, x, Nat.is_eq(T.Ent.k(e), x), {==}, gn)

# the puts leave a key the target lacks
def pt.puts_miss(+a: List<&2, T.Ent>, s: List<&2, T.Ent>, hit: Bool, +m: Maybe<&2, T.Ent>, +x: Nat, +gn: {T.get(s, x) == None{} : Maybe<&2, T.Ent>}) -> {pt.look(T.puts.go(a, s, hit), m, x) == m : Maybe<&2, T.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ne = pt.get_none_head(e, r, x, gn)
          pt.puts_miss(a, r, T.kept.at(a, r), m, x, Equal.trans(Maybe<&2, T.Ent>, T.get(r, x), T.get(e <> r, x), None{}, Equal.sym(Maybe<&2, T.Ent>, T.get(e <> r, x), T.get(r, x), pt.get_miss(e, r, x, ne)), gn))
        case False{}:
          +ne = pt.get_none_head(e, r, x, gn)
          %Equal.sym(Bool, Nat.is_eq(T.Ent.k(e), x), False{}, ne) : {pt.look(T.puts.go(a, r, T.kept.at(a, r)), pt.pick(_, Some{T.Ent{T.Ent.k(e), T.Ent.p(e), T.Ent.v(e)}}, m), x) == m : Maybe<&2, T.Ent>}
          pt.puts_miss(a, r, T.kept.at(a, r), m, x, Equal.trans(Maybe<&2, T.Ent>, T.get(r, x), T.get(e <> r, x), None{}, Equal.sym(Maybe<&2, T.Ent>, T.get(e <> r, x), T.get(r, x), pt.get_miss(e, r, x, ne)), gn))

def pt.ph_go(+a: List<&2, T.Ent>, +e: T.Ent, +r: List<&2, T.Ent>, +m: Maybe<&2, T.Ent>, +x: Nat, +z: T.Ent, c: Bool, +ec: {Nat.is_eq(T.Ent.k(e), x) == c : Bool}, hit: Bool, eh: {T.same(T.get(a, T.Ent.k(e)), Some{e}) == hit : Bool}, +al: {T.above(T.Ent.k(e), r) == True{} : Bool}, +sr: {T.sorted(r) == True{} : Bool}, ih: {T.get(r, x) == Some{z} : Maybe<&2, T.Ent>} -> {pt.look(T.puts.go(a, r, T.kept.at(a, r)), m, x) == pt.pick(T.same(T.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, T.Ent>}, +gs: {T.get(e <> r, x) == Some{z} : Maybe<&2, T.Ent>}) -> {pt.look(T.puts.go(a, e <> r, hit), m, x) == pt.pick(T.same(T.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, T.Ent>}:
  match c hit:
    case True{} True{}:
      +P = T.puts.go(a, r, T.kept.at(a, r))
      +ez = pt.some_inj(e, z, Equal.trans(Maybe<&2, T.Ent>, Some{e}, T.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, T.Ent>, T.get(e <> r, x), Some{e}, pt.get_hit(e, r, x, ec)), gs))
      %ez : {pt.look(P, m, x) == pt.pick(T.same(T.get(a, x), Some{_}), m, Some{_}) : Maybe<&2, T.Ent>}
      %pt.eq_true(T.Ent.k(e), x, ec) : {pt.look(P, m, _) == pt.pick(T.same(T.get(a, _), Some{e}), m, Some{e}) : Maybe<&2, T.Ent>}
      %Equal.sym(Bool, T.same(T.get(a, T.Ent.k(e)), Some{e}), True{}, eh) : {pt.look(P, m, T.Ent.k(e)) == pt.pick(_, m, Some{e}) : Maybe<&2, T.Ent>}
      pt.puts_miss(a, r, T.kept.at(a, r), m, T.Ent.k(e), pt.get_below(r, T.Ent.k(e), al, sr))
    case True{} False{}:
      +P = T.puts.go(a, r, T.kept.at(a, r))
      +E = {T.Ent{T.Ent.k(e), T.Ent.p(e), T.Ent.v(e)} : T.Ent}
      +ez = pt.some_inj(e, z, Equal.trans(Maybe<&2, T.Ent>, Some{e}, T.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, T.Ent>, T.get(e <> r, x), Some{e}, pt.get_hit(e, r, x, ec)), gs))
      %Equal.sym(Bool, Nat.is_eq(T.Ent.k(e), x), True{}, ec) : {pt.look(P, pt.pick(_, Some{E}, m), x) == pt.pick(T.same(T.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, T.Ent>}
      %ez : {pt.look(P, Some{E}, x) == pt.pick(T.same(T.get(a, x), Some{_}), m, Some{_}) : Maybe<&2, T.Ent>}
      %pt.eq_true(T.Ent.k(e), x, ec) : {pt.look(P, Some{E}, _) == pt.pick(T.same(T.get(a, _), Some{e}), m, Some{e}) : Maybe<&2, T.Ent>}
      %Equal.sym(Bool, T.same(T.get(a, T.Ent.k(e)), Some{e}), False{}, eh) : {pt.look(P, Some{E}, T.Ent.k(e)) == pt.pick(_, m, Some{e}) : Maybe<&2, T.Ent>}
      Equal.trans(Maybe<&2, T.Ent>, pt.look(P, Some{E}, T.Ent.k(e)), Some{E}, Some{e}, pt.puts_miss(a, r, T.kept.at(a, r), Some{E}, T.Ent.k(e), pt.get_below(r, T.Ent.k(e), al, sr)), Equal.cong(T.Ent, Maybe<&2, T.Ent>, y => Some{y}, E, e, pt.ent_eta(e)))
    case False{} True{}:
      ih(Equal.trans(Maybe<&2, T.Ent>, T.get(r, x), T.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, T.Ent>, T.get(e <> r, x), T.get(r, x), pt.get_miss(e, r, x, ec)), gs))
    case False{} False{}:
      +P = T.puts.go(a, r, T.kept.at(a, r))
      +E = {T.Ent{T.Ent.k(e), T.Ent.p(e), T.Ent.v(e)} : T.Ent}
      %Equal.sym(Bool, Nat.is_eq(T.Ent.k(e), x), False{}, ec) : {pt.look(P, pt.pick(_, Some{E}, m), x) == pt.pick(T.same(T.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, T.Ent>}
      ih(Equal.trans(Maybe<&2, T.Ent>, T.get(r, x), T.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, T.Ent>, T.get(e <> r, x), T.get(r, x), pt.get_miss(e, r, x, ec)), gs))

# the puts set a key the target holds, unless a holds it the same
def pt.puts_hit(+a: List<&2, T.Ent>, s: List<&2, T.Ent>, hit: Bool, eh: {T.kept.at(a, s) == hit : Bool}, +m: Maybe<&2, T.Ent>, +x: Nat, +z: T.Ent, +st: {T.sorted(s) == True{} : Bool}) -> {T.get(s, x) == Some{z} : Maybe<&2, T.Ent>} -> {pt.look(T.puts.go(a, s, hit), m, x) == pt.pick(T.same(T.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, T.Ent>}:
  match s:
    case Nil{}:
      gs => pt.none_some({pt.look(T.puts.go(a, Nil{}, hit), m, x) == pt.pick(T.same(T.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, T.Ent>}, z, gs)
    case +e <> +r:
      ih = pt.puts_hit(a, r, T.kept.at(a, r), {==}, m, x, z, pt.and_r(T.above(T.Ent.k(e), r), T.sorted(r), st))
      gs => pt.ph_go(a, e, r, m, x, z, Nat.is_eq(T.Ent.k(e), x), {==}, hit, eh, pt.and_l(T.above(T.Ent.k(e), r), T.sorted(r), st), pt.and_r(T.above(T.Ent.k(e), r), T.sorted(r), st), ih, gs)

def pt.reach_tail(+a: List<&2, T.Ent>, +x: Nat, +z: T.Ent, c: Bool, ec: {T.same(T.get(a, x), Some{z}) == c : Bool}) -> {pt.pick(c, T.get(a, x), Some{z}) == Some{z} : Maybe<&2, T.Ent>}:
  match c:
    case True{}:
      pt.same_some(T.get(a, x), z, ec)
    case False{}:
      {==}

def pt.reach_go(+a: List<&2, T.Ent>, +b: List<&2, T.Ent>, +x: Nat, +sb: {T.sorted(b) == True{} : Bool}, mb: Maybe<&2, T.Ent>, +eb: {T.get(b, x) == mb : Maybe<&2, T.Ent>}) -> {pt.look(T.puts.go(a, b, T.kept.at(a, b)), pt.look(T.dels.go(a, b, T.held.at(a, b)), T.get(a, x), x), x) == T.get(b, x) : Maybe<&2, T.Ent>}:
  match mb:
    case None{}:
      +P = T.puts.go(a, b, T.kept.at(a, b))
      +D = T.dels.go(a, b, T.held.at(a, b))
      +hb = Equal.cong(Maybe<&2, T.Ent>, Bool, mm => Maybe.is_some(&2, T.Ent, mm), T.get(b, x), None{}, eb)
      %Equal.sym(Maybe<&2, T.Ent>, pt.look(D, T.get(a, x), x), None{}, pt.dels_drop(a, b, T.held.at(a, b), {==}, x, hb)) : {pt.look(P, _, x) == T.get(b, x) : Maybe<&2, T.Ent>}
      Equal.trans(Maybe<&2, T.Ent>, pt.look(P, None{}, x), None{}, T.get(b, x), pt.puts_miss(a, b, T.kept.at(a, b), None{}, x, eb), Equal.sym(Maybe<&2, T.Ent>, T.get(b, x), None{}, eb))
    case Some{+z}:
      +P = T.puts.go(a, b, T.kept.at(a, b))
      +D = T.dels.go(a, b, T.held.at(a, b))
      +ga = T.get(a, x)
      +hb = Equal.cong(Maybe<&2, T.Ent>, Bool, mm => Maybe.is_some(&2, T.Ent, mm), T.get(b, x), Some{z}, eb)
      %Equal.sym(Maybe<&2, T.Ent>, pt.look(D, ga, x), ga, pt.dels_keep(a, b, T.held.at(a, b), {==}, ga, x, hb)) : {pt.look(P, _, x) == T.get(b, x) : Maybe<&2, T.Ent>}
      +c = T.same(ga, Some{z})
      Equal.trans(Maybe<&2, T.Ent>, pt.look(P, ga, x), pt.pick(c, ga, Some{z}), T.get(b, x), pt.puts_hit(a, b, T.kept.at(a, b), {==}, ga, x, z, sb)(eb), Equal.trans(Maybe<&2, T.Ent>, pt.pick(c, ga, Some{z}), Some{z}, T.get(b, x), pt.reach_tail(a, x, z, c, {==}), Equal.sym(Maybe<&2, T.Ent>, T.get(b, x), Some{z}, eb)))

# after the rewind ops, the tree holds at x what the target holds
def pt.reach_at(+a: List<&2, T.Ent>, +b: List<&2, T.Ent>, +x: Nat, +sb: {T.sorted(b) == True{} : Bool}) -> {T.get(T.patch(T.diff(a, b), a), x) == T.get(b, x) : Maybe<&2, T.Ent>}:
  +D = T.dels(a, b)
  +P = T.puts(a, b)
  +ga = T.get(a, x)
  Equal.trans(Maybe<&2, T.Ent>, T.get(T.patch(T.diff(a, b), a), x), pt.look(List.append(&2, T.Op, D, P), ga, x), T.get(b, x), pt.get_patch(T.diff(a, b), a, x), Equal.trans(Maybe<&2, T.Ent>, pt.look(List.append(&2, T.Op, D, P), ga, x), pt.look(P, pt.look(D, ga, x), x), T.get(b, x), pt.look_app(D, P, ga, x), pt.reach_go(a, b, x, sb, T.get(b, x), {==})))

# l1 and l2 hold the same node at the key of each node of es
def pt.Agree(es: List<&2, T.Ent>, +l1: List<&2, T.Ent>, +l2: List<&2, T.Ent>) -> Type:
  match es:
    case Nil{}:
      Unit
    case +e <> rest:
      ({T.get(l1, T.Ent.k(e)) == T.get(l2, T.Ent.k(e)) : Maybe<&2, T.Ent>} & pt.Agree(rest, l1, l2))

def pt.agree_reach(es: List<&2, T.Ent>, +a: List<&2, T.Ent>, +b: List<&2, T.Ent>, +sb: {T.sorted(b) == True{} : Bool}) -> pt.Agree(es, T.patch(T.diff(a, b), a), b):
  match es:
    case Nil{}:
      Unit{}
    case +e <> rest:
      (pt.reach_at(a, b, T.Ent.k(e), sb), pt.agree_reach(rest, a, b, sb))

# below two heads with one key, the lists agree as they did
def pt.agree_strip(es: List<&2, T.Ent>, +h1: T.Ent, +r1: List<&2, T.Ent>, +h2: T.Ent, +r2: List<&2, T.Ent>, ag: pt.Agree(es, h1 <> r1, h2 <> r2), +al: {T.above(T.Ent.k(h1), es) == True{} : Bool}, +st: {T.sorted(es) == True{} : Bool}, +keq: {T.Ent.k(h1) == T.Ent.k(h2) : Nat}) -> pt.Agree(es, r1, r2):
  match es:
    case Nil{}:
      Unit{}
    case +e <> +rest:
      (eq0, agt) = ag
      +k = T.Ent.k(e)
      +ne1 = pt.lt_ne(T.Ent.k(h1), k, al)
      +ne2 = pt.ne_at(T.Ent.k(h2), T.Ent.k(h1), k, Equal.sym(Nat, T.Ent.k(h1), T.Ent.k(h2), keq), ne1)
      +hd = Equal.trans(Maybe<&2, T.Ent>, T.get(r1, k), T.get(h1 <> r1, k), T.get(r2, k), Equal.sym(Maybe<&2, T.Ent>, T.get(h1 <> r1, k), T.get(r1, k), pt.get_miss(h1, r1, k, ne1)), Equal.trans(Maybe<&2, T.Ent>, T.get(h1 <> r1, k), T.get(h2 <> r2, k), T.get(r2, k), eq0, pt.get_miss(h2, r2, k, ne2)))
      (hd, pt.agree_strip(rest, h1, r1, h2, r2, agt, pt.above_tail(T.Ent.k(h1), e, rest, al, st), pt.and_r(T.above(k, rest), T.sorted(rest), st), keq))

# two sorted lists that agree have the same first key
def pt.ext_head(+h1: T.Ent, +r1: List<&2, T.Ent>, +h2: T.Ent, +r2: List<&2, T.Ent>, c: Cmp, ec: {Nat.cmp(T.Ent.k(h1), T.Ent.k(h2)) == c : Cmp}, e1: {T.get(h1 <> r1, T.Ent.k(h1)) == T.get(h2 <> r2, T.Ent.k(h1)) : Maybe<&2, T.Ent>}, e2: {T.get(h1 <> r1, T.Ent.k(h2)) == T.get(h2 <> r2, T.Ent.k(h2)) : Maybe<&2, T.Ent>}, +s1: {T.sorted(h1 <> r1) == True{} : Bool}, +s2: {T.sorted(h2 <> r2) == True{} : Bool}) -> {T.Ent.k(h1) == T.Ent.k(h2) : Nat}:
  match c:
    case LT{}:
      +gn = pt.get_below(h2 <> r2, T.Ent.k(h1), pt.cmp_lt(T.Ent.k(h1), T.Ent.k(h2), ec), s2)
      pt.some_none({T.Ent.k(h1) == T.Ent.k(h2) : Nat}, h1, Equal.trans(Maybe<&2, T.Ent>, Some{h1}, T.get(h1 <> r1, T.Ent.k(h1)), None{}, Equal.sym(Maybe<&2, T.Ent>, T.get(h1 <> r1, T.Ent.k(h1)), Some{h1}, pt.get_head(h1, r1)), Equal.trans(Maybe<&2, T.Ent>, T.get(h1 <> r1, T.Ent.k(h1)), T.get(h2 <> r2, T.Ent.k(h1)), None{}, e1, gn)))
    case EQ{}:
      pt.cmp_eq(T.Ent.k(h1), T.Ent.k(h2), ec)
    case GT{}:
      +gn = pt.get_below(h1 <> r1, T.Ent.k(h2), pt.cmp_gt(T.Ent.k(h1), T.Ent.k(h2), ec), s1)
      pt.none_some({T.Ent.k(h1) == T.Ent.k(h2) : Nat}, h2, Equal.trans(Maybe<&2, T.Ent>, None{}, T.get(h1 <> r1, T.Ent.k(h2)), Some{h2}, Equal.sym(Maybe<&2, T.Ent>, T.get(h1 <> r1, T.Ent.k(h2)), None{}, gn), Equal.trans(Maybe<&2, T.Ent>, T.get(h1 <> r1, T.Ent.k(h2)), T.get(h2 <> r2, T.Ent.k(h2)), Some{h2}, e2, pt.get_head(h2, r2))))

# two sorted lists that agree on their keys are equal
def pt.ext(l1: List<&2, T.Ent>, l2: List<&2, T.Ent>, +s1: {T.sorted(l1) == True{} : Bool}, +s2: {T.sorted(l2) == True{} : Bool}, A1: pt.Agree(l1, l1, l2), A2: pt.Agree(l2, l1, l2)) -> {l1 == l2 : List<&2, T.Ent>}:
  match l1 l2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+h2, +r2}:
      (e2, t2) = A2
      pt.none_some({Nil{} == h2 <> r2 : List<&2, T.Ent>}, h2, Equal.trans(Maybe<&2, T.Ent>, None{}, T.get(h2 <> r2, T.Ent.k(h2)), Some{h2}, e2, pt.get_head(h2, r2)))
    case Con{+h1, +r1} Nil{}:
      (e1, t1) = A1
      pt.some_none({h1 <> r1 == Nil{} : List<&2, T.Ent>}, h1, Equal.trans(Maybe<&2, T.Ent>, Some{h1}, T.get(h1 <> r1, T.Ent.k(h1)), None{}, Equal.sym(Maybe<&2, T.Ent>, T.get(h1 <> r1, T.Ent.k(h1)), Some{h1}, pt.get_head(h1, r1)), e1))
    case Con{+h1, +r1} Con{+h2, +r2}:
      (+e1, t1) = A1
      (+e2, t2) = A2
      +keq = pt.ext_head(h1, r1, h2, r2, Nat.cmp(T.Ent.k(h1), T.Ent.k(h2)), {==}, e1, e2, s1, s2)
      +s1t = pt.and_r(T.above(T.Ent.k(h1), r1), T.sorted(r1), s1)
      +s2t = pt.and_r(T.above(T.Ent.k(h2), r2), T.sorted(r2), s2)
      +al1 = pt.and_l(T.above(T.Ent.k(h1), r1), T.sorted(r1), s1)
      +al2 = Equal.trans(Bool, T.above(T.Ent.k(h1), r2), T.above(T.Ent.k(h2), r2), True{}, Equal.cong(Nat, Bool, n => T.above(n, r2), T.Ent.k(h1), T.Ent.k(h2), keq), pt.and_l(T.above(T.Ent.k(h2), r2), T.sorted(r2), s2))
      +ih = pt.ext(r1, r2, s1t, s2t, pt.agree_strip(r1, h1, r1, h2, r2, t1, al1, s1t, keq), pt.agree_strip(r2, h1, r1, h2, r2, t2, al2, s2t, keq))
      +hs = Equal.trans(Maybe<&2, T.Ent>, Some{h1}, T.get(h1 <> r1, T.Ent.k(h1)), Some{h2}, Equal.sym(Maybe<&2, T.Ent>, T.get(h1 <> r1, T.Ent.k(h1)), Some{h1}, pt.get_head(h1, r1)), Equal.trans(Maybe<&2, T.Ent>, T.get(h1 <> r1, T.Ent.k(h1)), T.get(h2 <> r2, T.Ent.k(h1)), Some{h2}, e1, pt.get_hit(h2, r2, T.Ent.k(h1), pt.eq_of(T.Ent.k(h1), T.Ent.k(h2), keq))))
      %pt.some_inj(h1, h2, hs) : {h1 <> r1 == _ <> r2 : List<&2, T.Ent>}
      %ih : {h1 <> r1 == h1 <> _ : List<&2, T.Ent>}
      {==}

def rewind_reaches(+a: List<&2, T.Ent>, +b: List<&2, T.Ent>, ga: {T.sound(a) == True{} : Bool}, +gb: {T.sound(b) == True{} : Bool}) -> {T.apply(a, T.Rewind{T.diff(a, b)}) == b : List<&2, T.Ent>}:
  +n = T.patch(T.diff(a, b), a)
  +sb = pt.and_l(T.sorted(b), T.rooted(b), gb)
  +sn = pt.sorted_patch(T.diff(a, b), a, pt.and_l(T.sorted(a), T.rooted(a), ga))
  +eq = pt.ext(n, b, sn, sb, pt.agree_reach(n, a, b, sb), pt.agree_reach(b, a, b, sb))
  %Equal.sym(List<&2, T.Ent>, n, b, eq) : {T.keep.at(T.sound(_), a, _) == b : List<&2, T.Ent>}
  %Equal.sym(Bool, T.sound(b), True{}, gb) : {T.keep.at(_, a, b) == b : List<&2, T.Ent>}
  {==}

# Delete: only below
# ------------------
# While prune walks the tree, every key in gone is x or below the rest
# of the walk, is not 0 (x is not the root; a node's key is above its
# parent's), and is not a key of the kept nodes; and every kept key is
# below the rest of the walk.

# f holds for every key of gone
def pt.All(gone: List<&2, Nat>, -f: Nat -> Bool) -> Data:
  match gone:
    case Nil{}:
      Unit
    case +g <> rest:
      Sigma<&2, &2, {f(g) == True{} : Bool}, _ => pt.All(rest, f)>

def pt.ah_go(+g: Nat, +gs: List<&2, Nat>, -f: Nat -> Bool, +y: Nat, c: Bool, ec: {Nat.is_eq(g, y) == c : Bool}, hd: {f(g) == True{} : Bool}, ih: {T.elem(gs, y) == True{} : Bool} -> {f(y) == True{} : Bool}, el: {T.elem(g <> gs, y) == True{} : Bool}) -> {f(y) == True{} : Bool}:
  match c:
    case True{}:
      %pt.eq_true(g, y, ec) : {f(_) == True{} : Bool}
      hd
    case False{}:
      ih(Equal.trans(Bool, T.elem(gs, y), Bool.or(Nat.is_eq(g, y), T.elem(gs, y)), True{}, Equal.cong(Bool, Bool, w => Bool.or(w, T.elem(gs, y)), False{}, Nat.is_eq(g, y), Equal.sym(Bool, Nat.is_eq(g, y), False{}, ec)), el))

def pt.all_hit(gone: List<&2, Nat>, -f: Nat -> Bool, +y: Nat, a: pt.All(gone, f)) -> {T.elem(gone, y) == True{} : Bool} -> {f(y) == True{} : Bool}:
  match gone:
    case Nil{}:
      el => pt.absurdF({f(y) == True{} : Bool}, el)
    case +g <> +gs:
      (hd, tl) = a
      ih = pt.all_hit(gs, f, y, tl)
      el => pt.ah_go(g, gs, f, y, Nat.is_eq(g, y), {==}, hd, ih, el)

def pt.or_above_tail(c: Bool, +g: Nat, +e: T.Ent, +r: List<&2, T.Ent>, h: {Bool.or(c, T.above(g, e <> r)) == True{} : Bool}, +st: {T.sorted(e <> r) == True{} : Bool}) -> {Bool.or(c, T.above(g, r)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pt.above_tail(g, e, r, h, st)

def pt.gl_tail(gone: List<&2, Nat>, +x: Nat, +e: T.Ent, +r: List<&2, T.Ent>, a: pt.All(gone, z => Bool.or(Nat.is_eq(z, x), T.above(z, e <> r))), +st: {T.sorted(e <> r) == True{} : Bool}) -> pt.All(gone, z => Bool.or(Nat.is_eq(z, x), T.above(z, r))):
  match gone:
    case Nil{}:
      Unit{}
    case +g <> +gs:
      (hd, tl) = a
      (pt.or_above_tail(Nat.is_eq(g, x), g, e, r, hd, st), pt.gl_tail(gs, x, e, r, tl, st))

def pt.not_f(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      pt.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pt.not_t(+b: Bool, h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

def pt.not_has_app(+B: List<&2, T.Ent>, +C: List<&2, T.Ent>, +y: Nat, nb: {T.has(B, y) == False{} : Bool}, nc: {T.has(C, y) == False{} : Bool}) -> {Bool.not(T.has(List.append(&2, T.Ent, B, C), y)) == True{} : Bool}:
  %Equal.sym(Bool, T.has(List.append(&2, T.Ent, B, C), y), Bool.or(T.has(B, y), T.has(C, y)), pt.has_app(B, C, y)) : {Bool.not(_) == True{} : Bool}
  %Equal.sym(Bool, T.has(B, y), False{}, nb) : {Bool.not(Bool.or(_, T.has(C, y))) == True{} : Bool}
  %Equal.sym(Bool, T.has(C, y), False{}, nc) : {Bool.not(Bool.or(False{}, _)) == True{} : Bool}
  {==}

def pt.ng_snoc(gone: List<&2, Nat>, +B: List<&2, T.Ent>, +e: T.Ent, a: pt.All(gone, z => Bool.not(T.has(B, z))), +ne: {T.elem(gone, T.Ent.k(e)) == False{} : Bool}) -> pt.All(gone, z => Bool.not(T.has(List.append(&2, T.Ent, B, [e]), z))):
  match gone:
    case Nil{}:
      Unit{}
    case +g <> +gs:
      (hd, tl) = a
      +ng = pt.or_l(Nat.is_eq(g, T.Ent.k(e)), T.elem(gs, T.Ent.k(e)), ne)
      +nc = pt.has_miss(e, Nil{}, g, pt.ne_comm(g, T.Ent.k(e), ng))
      (pt.not_has_app(B, [e], g, pt.not_f(T.has(B, g), hd), nc), pt.ng_snoc(gs, B, e, tl, pt.or_r(Nat.is_eq(g, T.Ent.k(e)), T.elem(gs, T.Ent.k(e)), ne)))

# every kept node is below the rest of the walk
def pt.blw(B: List<&2, T.Ent>, +s: List<&2, T.Ent>) -> Bool:
  match B:
    case Nil{}:
      True{}
    case +b <> rest:
      Bool.and(T.above(T.Ent.k(b), s), pt.blw(rest, s))

def pt.blw_tail(B: List<&2, T.Ent>, +e: T.Ent, +r: List<&2, T.Ent>, +bw: {pt.blw(B, e <> r) == True{} : Bool}, +st: {T.sorted(e <> r) == True{} : Bool}) -> {pt.blw(B, r) == True{} : Bool}:
  match B:
    case Nil{}:
      {==}
    case +b <> +bs:
      +i = T.above(T.Ent.k(b), e <> r)
      pt.and_t(T.above(T.Ent.k(b), r), pt.blw(bs, r), pt.above_tail(T.Ent.k(b), e, r, pt.and_l(i, pt.blw(bs, e <> r), bw), st), pt.blw_tail(bs, e, r, pt.and_r(i, pt.blw(bs, e <> r), bw), st))

def pt.blw_snoc(B: List<&2, T.Ent>, +e: T.Ent, +r: List<&2, T.Ent>, +bw: {pt.blw(B, r) == True{} : Bool}, +ae: {T.above(T.Ent.k(e), r) == True{} : Bool}) -> {pt.blw(List.append(&2, T.Ent, B, [e]), r) == True{} : Bool}:
  match B:
    case Nil{}:
      pt.and_t(T.above(T.Ent.k(e), r), True{}, ae, {==})
    case +b <> +bs:
      +i = T.above(T.Ent.k(b), r)
      pt.and_t(i, pt.blw(List.append(&2, T.Ent, bs, [e]), r), pt.and_l(i, pt.blw(bs, r), bw), pt.blw_snoc(bs, e, r, pt.and_r(i, pt.blw(bs, r), bw), ae))

def pt.blw_has(B: List<&2, T.Ent>, +e: T.Ent, +r: List<&2, T.Ent>, +bw: {pt.blw(B, e <> r) == True{} : Bool}) -> {T.has(B, T.Ent.k(e)) == False{} : Bool}:
  match B:
    case Nil{}:
      {==}
    case +b <> +bs:
      +i = T.above(T.Ent.k(b), e <> r)
      +ne = pt.lt_ne(T.Ent.k(b), T.Ent.k(e), pt.and_l(i, pt.blw(bs, e <> r), bw))
      Equal.trans(Bool, T.has(b <> bs, T.Ent.k(e)), T.has(bs, T.Ent.k(e)), False{}, pt.has_miss(b, bs, T.Ent.k(e), ne), pt.blw_has(bs, e, r, pt.and_r(i, pt.blw(bs, e <> r), bw)))

def pt.lt_zero(-A: Type, p: Nat, lt: {Nat.is_lt(p, 0n) == True{} : Bool}) -> A:
  match p:
    case 0n:
      pt.absurdF(A, lt)
    case 1n+q:
      pt.absurdF(A, lt)

# a key above a parent is not the root
def pt.lt_nz(+p: Nat, k: Nat, lt: {Nat.is_lt(p, k) == True{} : Bool}) -> {Bool.not(Nat.is_eq(k, 0n)) == True{} : Bool}:
  match k:
    case 0n:
      pt.lt_zero({Bool.not(Nat.is_eq(0n, 0n)) == True{} : Bool}, p, lt)
    case 1n+q:
      {==}

def pt.above_lt(+a: Nat, +b: Nat, r: List<&2, T.Ent>, ab: {Nat.is_lt(a, b) == True{} : Bool}, br: {T.above(b, r) == True{} : Bool}) -> {T.above(a, r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +h <> +rest:
      pt.lt_trans(a, b, T.Ent.k(h), ab, br)

def pt.ob_drop(+gone: List<&2, Nat>, +x: Nat, +B: List<&2, T.Ent>, +e: T.Ent, +r: List<&2, T.Ent>, c: Bool, ec: {T.elem(gone, T.Ent.k(e)) == c : Bool}, +eh: {Bool.or(c, T.elem(gone, T.Ent.p(e))) == True{} : Bool}, +i1: pt.All(gone, z => Bool.or(Nat.is_eq(z, x), T.above(z, e <> r))), +i2: pt.All(gone, z => Bool.not(Nat.is_eq(z, 0n))), +i3: pt.All(gone, z => Bool.not(T.has(B, z))), +lt: {Nat.is_lt(T.Ent.p(e), T.Ent.k(e)) == True{} : Bool}, +st: {T.sorted(e <> r) == True{} : Bool}) -> {Bool.or(Nat.is_eq(T.Ent.k(e), x), Bool.and(Bool.not(Nat.is_eq(T.Ent.p(e), 0n)), Bool.not(T.has(List.append(&2, T.Ent, B, T.prune.go(r, T.Ent.k(e) <> gone, T.gone.at(r, T.Ent.k(e) <> gone))), T.Ent.p(e))))) == True{} : Bool}:
  match c:
    case True{}:
      +k = T.Ent.k(e)
      +p = T.Ent.p(e)
      +g2 = {k <> gone : List<&2, Nat>}
      +R = List.append(&2, T.Ent, B, T.prune.go(r, g2, T.gone.at(r, g2)))
      +d = Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(T.has(R, p)))
      +h = pt.all_hit(gone, z => Bool.or(Nat.is_eq(z, x), T.above(z, e <> r)), k, i1)(ec)
      pt.or_tl(Nat.is_eq(k, x), d, pt.or_l_true(Nat.is_eq(k, x), Nat.is_lt(k, k), h, pt.lt_irrefl(k)))
    case False{}:
      +k = T.Ent.k(e)
      +p = T.Ent.p(e)
      +g2 = {k <> gone : List<&2, Nat>}
      +P = T.prune.go(r, g2, T.gone.at(r, g2))
      +R = List.append(&2, T.Ent, B, P)
      +d = Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(T.has(R, p)))
      +nz = pt.all_hit(gone, z => Bool.not(Nat.is_eq(z, 0n)), p, i2)(eh)
      +nb = pt.all_hit(gone, z => Bool.not(T.has(B, z)), p, i3)(eh)
      +sr = pt.and_r(T.above(k, r), T.sorted(r), st)
      +ap = pt.above_prune_go(r, g2, T.gone.at(r, g2), p, pt.above_lt(p, k, r, lt, pt.and_l(T.above(k, r), T.sorted(r), st)), sr)
      +np = pt.has_below(P, p, ap, pt.sorted_prune_go(r, g2, T.gone.at(r, g2), sr))
      pt.or_tr(Nat.is_eq(k, x), d, pt.and_t(Bool.not(Nat.is_eq(p, 0n)), Bool.not(T.has(R, p)), nz, pt.not_has_app(B, P, p, pt.not_f(T.has(B, p), nb), np)))

def pt.ob_go(s: List<&2, T.Ent>, +gone: List<&2, Nat>, hit: Bool, eh: {T.gone.at(s, gone) == hit : Bool}, +x: Nat, +t: List<&2, T.Ent>, +B: List<&2, T.Ent>, +i1: pt.All(gone, z => Bool.or(Nat.is_eq(z, x), T.above(z, s))), +i2: pt.All(gone, z => Bool.not(Nat.is_eq(z, 0n))), +i3: pt.All(gone, z => Bool.not(T.has(B, z))), +bw: {pt.blw(B, s) == True{} : Bool}, +st: {T.sorted(s) == True{} : Bool}, +rs: {T.rooted.go(s, t) == True{} : Bool}) -> {T.only_below(s, x, List.append(&2, T.Ent, B, T.prune.go(s, gone, hit))) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +k = T.Ent.k(e)
          +p = T.Ent.p(e)
          +g2 = {k <> gone : List<&2, Nat>}
          +R = List.append(&2, T.Ent, B, T.prune.go(r, g2, T.gone.at(r, g2)))
          +lt = pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), T.has(t, p)), pt.and_l(T.ok(t, k, p), T.rooted.go(r, t), rs))
          +ak = pt.and_l(T.above(k, r), T.sorted(r), st)
          +hd = pt.or_tr(T.has(R, k), Bool.or(Nat.is_eq(k, x), Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(T.has(R, p)))), pt.ob_drop(gone, x, B, e, r, T.elem(gone, k), {==}, eh, i1, i2, i3, lt, st))
          +j1 = {(pt.or_tr(Nat.is_eq(k, x), T.above(k, r), ak), pt.gl_tail(gone, x, e, r, i1, st)) : pt.All(g2, z => Bool.or(Nat.is_eq(z, x), T.above(z, r)))}
          +j2 = {(pt.lt_nz(p, k, lt), i2) : pt.All(g2, z => Bool.not(Nat.is_eq(z, 0n)))}
          +j3 = {(pt.not_t(T.has(B, k), pt.blw_has(B, e, r, bw)), i3) : pt.All(g2, z => Bool.not(T.has(B, z)))}
          +tl = pt.ob_go(r, g2, T.gone.at(r, g2), {==}, x, t, B, j1, j2, j3, pt.blw_tail(B, e, r, bw, st), pt.and_r(T.above(k, r), T.sorted(r), st), pt.and_r(T.ok(t, k, p), T.rooted.go(r, t), rs))
          pt.and_t(Bool.or(T.has(R, k), Bool.or(Nat.is_eq(k, x), Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(T.has(R, p))))), T.only_below(r, x, R), hd, tl)
        case False{}:
          +k = T.Ent.k(e)
          +p = T.Ent.p(e)
          +P = T.prune.go(r, gone, T.gone.at(r, gone))
          +R = List.append(&2, T.Ent, B, e <> P)
          +B2 = List.append(&2, T.Ent, B, [e])
          +ak = pt.and_l(T.above(k, r), T.sorted(r), st)
          +hd = pt.or_tl(T.has(R, k), Bool.or(Nat.is_eq(k, x), Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(T.has(R, p)))), pt.has_app_r(B, e <> P, k, pt.has_head(e, P)))
          +j3 = pt.ng_snoc(gone, B, e, i3, pt.or_l(T.elem(gone, k), T.elem(gone, p), eh))
          +bw2 = pt.blw_snoc(B, e, r, pt.blw_tail(B, e, r, bw, st), ak)
          +ih = pt.ob_go(r, gone, T.gone.at(r, gone), {==}, x, t, B2, pt.gl_tail(gone, x, e, r, i1, st), i2, j3, bw2, pt.and_r(T.above(k, r), T.sorted(r), st), pt.and_r(T.ok(t, k, p), T.rooted.go(r, t), rs))
          +tl = Equal.trans(Bool, T.only_below(r, x, R), T.only_below(r, x, List.append(&2, T.Ent, B2, P)), True{}, Equal.cong(List<&2, T.Ent>, Bool, l => T.only_below(r, x, l), R, List.append(&2, T.Ent, B2, P), Equal.sym(List<&2, T.Ent>, List.append(&2, T.Ent, B2, P), R, pt.app_snoc(B, e, P))), ih)
          pt.and_t(Bool.or(T.has(R, k), Bool.or(Nat.is_eq(k, x), Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(T.has(R, p))))), T.only_below(r, x, R), hd, tl)

# a prune of a node (not the root) removes only its subtree
def pt.only_below_nz(+t: List<&2, T.Ent>, +good: {T.sound(t) == True{} : Bool}, +x: Nat, nz: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {T.only_below(t, x, T.prune(t, x)) == True{} : Bool}:
  +i1 = {(pt.or_tl(Nat.is_eq(x, x), T.above(x, t), Equal.sym(Bool, True{}, Nat.is_eq(x, x), pt.eq_refl(x))), Unit{}) : pt.All([x], z => Bool.or(Nat.is_eq(z, x), T.above(z, t)))}
  +i2 = {(pt.not_t(Nat.is_eq(x, 0n), nz), Unit{}) : pt.All([x], z => Bool.not(Nat.is_eq(z, 0n)))}
  +i3 = {({==}, Unit{}) : pt.All([x], z => Bool.not(T.has(Nil{}, z)))}
  pt.ob_go(t, [x], T.gone.at(t, [x]), {==}, x, t, Nil{}, i1, i2, i3, {==}, pt.and_l(T.sorted(t), T.rooted(t), good), pt.and_r(T.sorted(t), T.rooted(t), good))

# a tree that keeps every node drops none
def pt.ob_all(s: List<&2, T.Ent>, +x: Nat, +r: List<&2, T.Ent>, +ah: {pt.allhas(s, r) == True{} : Bool}) -> {T.only_below(s, x, r) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +i = T.has(r, T.Ent.k(e))
      +o = Bool.or(Nat.is_eq(T.Ent.k(e), x), Bool.and(Bool.not(Nat.is_eq(T.Ent.p(e), 0n)), Bool.not(T.has(r, T.Ent.p(e)))))
      pt.and_t(Bool.or(i, o), T.only_below(rest, x, r), pt.or_tl(i, o, pt.and_l(i, pt.allhas(rest, r), ah)), pt.ob_all(rest, x, r, pt.and_r(i, pt.allhas(rest, r), ah)))

# a delete of the root changes nothing; of a node, removes its subtree
def delete_only_below(+t: List<&2, T.Ent>, +good: {T.sound(t) == True{} : Bool}, +x: Nat) -> {T.only_below(t, x, T.apply(t, T.Do{T.Del{x}})) == True{} : Bool}:
  match x:
    case 0n:
      pt.ob_all(t, 0n, t, pt.allhas_self(t))
    case 1n+y:
      pt.only_below_nz(t, good, 1n+y, {==})
