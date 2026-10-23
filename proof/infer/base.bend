# eukhe: lemmas the proofs of area infer share

import Base
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../bend/ffi_infer.bend as FIn
import ../../LAWS.bend as Laws
import ../base.bend as L

def pi.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : L.pi.BD(_, Unit, A)
  Unit{}

def pi.void(-A: Type, e: Empty) -> A:
  match e:

def pi.flip(-a: Bool, h: {a == True{} : Bool}, g: {a == False{} : Bool}) -> Empty:
  pi.absurd(Empty, Equal.trans(Bool, True{}, a, False{}, Equal.sym(Bool, a, True{}, h), g))

def pi.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      L.pi.absurdF({False{} == True{} : Bool}, h)

def pi.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      L.pi.absurdF({b == True{} : Bool}, h)

# Forced calls
# ------------

def pi.fst_next(-t: If.Try, p: List<&2, If.Try> & If.Forced) -> {t <> Pair.fst(List<&2, If.Try>, If.Forced, p) == Pair.fst(List<&2, If.Try>, If.Forced, If.force.next(t, p)) : List<&2, If.Try>}:
  (ts, o) = p
  {==}

# Numbers
# -------

def pi.le_trans(a: Nat, b: Nat, c: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      L.pi.le0(c)
    case 1n+p 0n _:
      L.pi.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      L.pi.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pi.le_trans(p, q, r, ab, bc)

def pi.add_zero(+a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, p, Nat.add(p, 0n), pi.add_zero(p))

def pi.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), pi.add_succ(p, b))

def pi.or_r_true(a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}, +ea: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      pi.absurd({b == True{} : Bool}, ea)
    case False{}:
      h

# one chunk more: each and the counter take the same step
def pi.each_step(b: Bool, +x: Nat, +rest: List<&2, Nat>, +q: Nat, +n: Nat, +ih: {If.each(rest, q, n) == Nat.is_le(n, If.cycle(rest, q)) : Bool}) -> {Bool.and(b, If.each(rest, q, n)) == Nat.is_le(1n+n, If.cycle.go(x <> rest, q, b)) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# the first m chunks each equal the chunk 1+q before them exactly when the
# counter of period 1+q is at least m
def pi.each_cycle(+s: List<&2, Nat>, +q: Nat, +m: Nat) -> {If.each(s, q, m) == Nat.is_le(m, If.cycle(s, q)) : Bool}:
  match s m:
    case _ 0n:
      Equal.sym(Bool, Nat.is_le(0n, If.cycle(s, q)), True{}, L.pi.le0(If.cycle(s, q)))
    case Nil{} 1n+n:
      {==}
    case x <> rest 1n+n:
      pi.each_step(If.back(rest, q, x), x, rest, q, n, pi.each_cycle(rest, q, n))

# the counters fire exactly when the window is periodic
def pi.fires_periodic(+s: List<&2, Nat>, +k: Nat, +n: Nat) -> {If.fires.go(s, k, n) == If.periodic.go(s, k, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      %pi.each_cycle(s, q, Nat.sub(k, 1n+q)) : {Bool.or(_, If.fires.go(s, k, q)) == Bool.or(If.each(s, q, Nat.sub(k, 1n+q)), If.periodic.go(s, k, q)) : Bool}
      %Equal.sym(Bool, If.fires.go(s, k, q), If.periodic.go(s, k, q), pi.fires_periodic(s, k, q)) : {Bool.or(If.each(s, q, Nat.sub(k, 1n+q)), _) == Bool.or(If.each(s, q, Nat.sub(k, 1n+q)), If.periodic.go(s, k, q)) : Bool}
      {==}

# a guard that has not cut yet cuts a stream with a periodic window
def pi.cut_go(+xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>, +n: Nat, hit: Bool, +eh: {If.fire.at(xs, k, seen) == hit : Bool}, +lp: {If.loops.go(xs, k, seen) == True{} : Bool}) -> {If.Cut.cut(If.guard.go(xs, k, seen, n, hit)) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.pi.absurdF({If.Cut.cut(If.guard.go(Nil{}, k, seen, n, hit)) == True{} : Bool}, lp)
    case x <> rest:
      match hit:
        case True{}:
          {==}
        case False{}:
          +ep = Equal.trans(Bool, If.periodic(x <> seen, k), If.fires(x <> seen, k), False{}, Equal.sym(Bool, If.fires(x <> seen, k), If.periodic(x <> seen, k), pi.fires_periodic(x <> seen, k, If.periods(k))), eh)
          pi.cut_go(rest, k, x <> seen, 1n+n, If.fire.at(rest, k, x <> seen), {==}, pi.or_r_true(If.periodic(x <> seen, k), If.loops.go(rest, k, x <> seen), lp, ep))

def pq.flip(-A: Type, -a: Bool, h: {a == True{} : Bool}, g: {a == False{} : Bool}) -> A:
  L.pq.absurd(A, Equal.trans(Bool, True{}, a, False{}, Equal.sym(Bool, a, True{}, h), g))

def pq.and_t(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pq.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the right side of a false and whose left side holds
def pq.and_tf(a: Bool, -b: Bool, h: {Bool.and(a, b) == False{} : Bool}, ha: {a == True{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      L.pq.absurdF({b == False{} : Bool}, ha)

def pq.or_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      L.pq.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pq.or_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      L.pq.absurd({b == False{} : Bool}, h)
    case False{}:
      h

# the right side of a true or whose left side fails
def pq.or_fl(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, na: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      L.pq.absurd({b == True{} : Bool}, na)
    case False{}:
      h

def pq.not_f(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      L.pq.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# x, y hold and and(x, and(y, not z)) fails: z holds
def pq.ncv(x: Bool, y: Bool, z: Bool, nc: {Bool.and(x, Bool.and(y, Bool.not(z))) == False{} : Bool}, hx: {x == True{} : Bool}, hy: {y == True{} : Bool}) -> {z == True{} : Bool}:
  match x y z:
    case False{} _ _:
      L.pq.absurdF({z == True{} : Bool}, hx)
    case True{} False{} _:
      L.pq.absurdF({z == True{} : Bool}, hy)
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      L.pq.absurd({False{} == True{} : Bool}, nc)

# Numbers
# -------

def pq.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pq.eq_refl(p)

def pq.eq_of(+a: Nat, +b: Nat, ab: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %ab : {Nat.is_eq(a, _) == True{} : Bool}
  Equal.sym(Bool, True{}, Nat.is_eq(a, a), pq.eq_refl(a))

def pq.eq_tr(+x: Nat, +y: Nat, +z: Nat, xz: {Nat.is_eq(x, z) == True{} : Bool}, yz: {Nat.is_eq(y, z) == True{} : Bool}) -> {Nat.is_eq(x, y) == True{} : Bool}:
  %Equal.sym(Nat, y, z, L.pq.eq_true(y, z, yz)) : {Nat.is_eq(x, _) == True{} : Bool}
  xz

# neither below the other: equal
def pq.tri(x: Nat, y: Nat, n1: {Nat.is_lt(y, x) == False{} : Bool}, n2: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_eq(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      L.pq.absurd({Nat.is_eq(0n, 1n+q) == True{} : Bool}, n2)
    case 1n+p 0n:
      L.pq.absurd({Nat.is_eq(1n+p, 0n) == True{} : Bool}, n1)
    case 1n+p 1n+q:
      pq.tri(p, q, n1, n2)

def pq.lt_le(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Equal.sym(Bool, Nat.is_le(0n, q), True{}, L.pq.le0(q))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pq.lt_le(p, q)

def pq.lt_at(-k: Nat, -x: Nat, -y: Nat, e: {k == x : Nat}, h: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_lt(k, y) == False{} : Bool}:
  %Equal.sym(Nat, k, x, e) : {Nat.is_lt(_, y) == False{} : Bool}
  h

# Lookup: none and some
# ---------------------

def pq.none_go(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +b: Maybe<&2, If.Best>, hit: Bool, eh: {If.use.at(rs, q, d) == hit : Bool}, none: {If.any_at(rs, q, d, 0n) == False{} : Bool}) -> {If.look.go(rs, q, d, b, hit) == b : Maybe<&2, If.Best>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      match hit:
        case True{}:
          +H = Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), d))
          +z = Nat.is_le(0n, If.Rule.rank(r))
          +le = pq.and_tf(H, z, pq.or_l(Bool.and(H, z), If.any_at(rest, q, d, 0n), none), eh)
          pq.flip({If.look.go(r <> rest, q, d, b, True{}) == b : Maybe<&2, If.Best>}, z, L.pq.le0(If.Rule.rank(r)), le)
        case False{}:
          +H = Bool.and(Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), d)), Nat.is_le(0n, If.Rule.rank(r)))
          pq.none_go(rest, q, d, b, If.use.at(rest, q, d), {==}, pq.or_r(H, If.any_at(rest, q, d, 0n), none))

def pq.quirk_unknown_when_none(+rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, none: {If.any_at(rs, q, d, 0n) == False{} : Bool}) -> {If.lookup(rs, q, d) == If.Unknown{} : If.Ans}:
  %Equal.sym(Maybe<&2, If.Best>, If.look.go(rs, q, d, None{}, If.use.at(rs, q, d)), None{}, pq.none_go(rs, q, d, None{}, If.use.at(rs, q, d), {==}, none)) : {If.ans(_) == If.Unknown{} : If.Ans}
  {==}

# Two rules that apply
# --------------------

def pq.val_of(+ta: Nat, +tb: Nat, +da: Nat, +db: Nat, +va: Nat, +vb: Nat, +f: Nat, +d: Nat, nc: {Bool.and(Nat.is_eq(ta, tb), Bool.and(Nat.is_eq(da, db), Bool.not(Nat.is_eq(va, vb)))) == False{} : Bool}, af: {Nat.is_eq(ta, f) == True{} : Bool}, bf: {Nat.is_eq(tb, f) == True{} : Bool}, ad: {Nat.is_eq(da, d) == True{} : Bool}, bd: {Nat.is_eq(db, d) == True{} : Bool}) -> {va == vb : Nat}:
  L.pq.eq_true(va, vb, pq.ncv(Nat.is_eq(ta, tb), Nat.is_eq(da, db), Nat.is_eq(va, vb), nc, pq.eq_tr(ta, tb, f, af, bf), pq.eq_tr(da, db, d, ad, bd)))

# two rules of one rank that apply with one directive and do not clash
# have one value
def pq.same_val(+q: If.Query, +a: If.Rule, +b: If.Rule, +d: Nat, nc: {If.clash(a, b) == False{} : Bool}, +ha: {Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d)) == True{} : Bool}, +hb: {Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d)) == True{} : Bool}, er: {Nat.is_eq(If.Rule.rank(a), If.Rule.rank(b)) == True{} : Bool}) -> {If.Rule.val(a) == If.Rule.val(b) : Nat}:
  match q a b:
    case If.Query{+f, m, h} If.Rule{If.Fam{}, +ta, +da, +va} If.Rule{If.Fam{}, +tb, +db, +vb}:
      pq.val_of(ta, tb, da, db, va, vb, f, d, nc, L.pq.and_l(Nat.is_eq(ta, f), Nat.is_eq(da, d), ha), L.pq.and_l(Nat.is_eq(tb, f), Nat.is_eq(db, d), hb), L.pq.and_r(Nat.is_eq(ta, f), Nat.is_eq(da, d), ha), L.pq.and_r(Nat.is_eq(tb, f), Nat.is_eq(db, d), hb))
    case If.Query{f, +m, h} If.Rule{If.Mod{}, +ta, +da, +va} If.Rule{If.Mod{}, +tb, +db, +vb}:
      pq.val_of(ta, tb, da, db, va, vb, m, d, nc, L.pq.and_l(Nat.is_eq(ta, m), Nat.is_eq(da, d), ha), L.pq.and_l(Nat.is_eq(tb, m), Nat.is_eq(db, d), hb), L.pq.and_r(Nat.is_eq(ta, m), Nat.is_eq(da, d), ha), L.pq.and_r(Nat.is_eq(tb, m), Nat.is_eq(db, d), hb))
    case If.Query{f, m, +h} If.Rule{If.Host{}, +ta, +da, +va} If.Rule{If.Host{}, +tb, +db, +vb}:
      pq.val_of(ta, tb, da, db, va, vb, h, d, nc, L.pq.and_l(Nat.is_eq(ta, h), Nat.is_eq(da, d), ha), L.pq.and_l(Nat.is_eq(tb, h), Nat.is_eq(db, d), hb), L.pq.and_r(Nat.is_eq(ta, h), Nat.is_eq(da, d), ha), L.pq.and_r(Nat.is_eq(tb, h), Nat.is_eq(db, d), hb))
    case If.Query{f, m, h} If.Rule{If.Fam{}, ta, da, va} If.Rule{If.Mod{}, tb, db, vb}:
      L.pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Fam{}, ta, da, va} If.Rule{If.Host{}, tb, db, vb}:
      L.pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Mod{}, ta, da, va} If.Rule{If.Fam{}, tb, db, vb}:
      L.pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Mod{}, ta, da, va} If.Rule{If.Host{}, tb, db, vb}:
      L.pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Host{}, ta, da, va} If.Rule{If.Fam{}, tb, db, vb}:
      L.pq.absurdF({va == vb : Nat}, er)
    case If.Query{f, m, h} If.Rule{If.Host{}, ta, da, va} If.Rule{If.Mod{}, tb, db, vb}:
      L.pq.absurdF({va == vb : Nat}, er)

# The highest layer wins
# ----------------------

# before r: the best is below r's rank, or at it with r's value
def pq.pre_ok(b: Maybe<&2, If.Best>, +r: If.Rule) -> Bool:
  match b:
    case None{}:
      True{}
    case Some{x}:
      match x:
        case If.Best{+k, v}:
          Bool.or(Nat.is_lt(k, If.Rule.rank(r)), Bool.and(Nat.is_eq(k, If.Rule.rank(r)), Nat.is_eq(v, If.Rule.val(r))))

# from r on: the best is at r's rank with r's value
def pq.good(b: Maybe<&2, If.Best>, +r: If.Rule) -> Bool:
  match b:
    case None{}:
      False{}
    case Some{x}:
      match x:
        case If.Best{k, v}:
          Bool.and(Nat.is_eq(k, If.Rule.rank(r)), Nat.is_eq(v, If.Rule.val(r)))

def pq.good_ans(b: Maybe<&2, If.Best>, +r: If.Rule, g: {pq.good(b, r) == True{} : Bool}) -> {If.ans(b) == If.Known{If.Rule.val(r)} : If.Ans}:
  match b:
    case None{}:
      L.pq.absurdF({If.ans(None{}) == If.Known{If.Rule.val(r)} : If.Ans}, g)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          +ev = L.pq.eq_true(v, If.Rule.val(r), L.pq.and_r(Nat.is_eq(k, If.Rule.rank(r)), Nat.is_eq(v, If.Rule.val(r)), g))
          Equal.cong(Nat, If.Ans, z => If.Known{z}, v, If.Rule.val(r), ev)

def pq.good_fresh(+r: If.Rule) -> {pq.good(Some{If.Best{If.Rule.rank(r), If.Rule.val(r)}}, r) == True{} : Bool}:
  +R = If.Rule.rank(r)
  +V = If.Rule.val(r)
  %pq.eq_refl(R) : {Bool.and(_, Nat.is_eq(V, V)) == True{} : Bool}
  %pq.eq_refl(V) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

def pq.post_step(b: Maybe<&2, If.Best>, +s: If.Rule, +r: If.Rule, +gb: {pq.good(b, r) == True{} : Bool}, ns: {Nat.is_lt(If.Rule.rank(r), If.Rule.rank(s)) == False{} : Bool}) -> {pq.good(If.better(b, s), r) == True{} : Bool}:
  match b:
    case None{}:
      L.pq.absurdF({pq.good(If.better(None{}, s), r) == True{} : Bool}, gb)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          +R = If.Rule.rank(r)
          +ek = L.pq.eq_true(k, R, L.pq.and_l(Nat.is_eq(k, R), Nat.is_eq(v, If.Rule.val(r)), gb))
          +lk = pq.lt_at(k, R, If.Rule.rank(s), ek, ns)
          %Equal.sym(Bool, Nat.is_lt(k, If.Rule.rank(s)), False{}, lk) : {pq.good(If.better.at(_, If.Best{k, v}, s), r) == True{} : Bool}
          gb

def pq.post_go(rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, +r: If.Rule, +b: Maybe<&2, If.Best>, hit: Bool, eh: {If.use.at(rs, q, d) == hit : Bool}, gb: {pq.good(b, r) == True{} : Bool}, +top: {If.any_at(rs, q, d, 1n+If.Rule.rank(r)) == False{} : Bool}) -> {pq.good(If.look.go(rs, q, d, b, hit), r) == True{} : Bool}:
  match rs:
    case Nil{}:
      gb
    case +s <> +rest:
      match hit:
        case True{}:
          +R = If.Rule.rank(r)
          +H = Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), d))
          +z = Nat.is_le(1n+R, If.Rule.rank(s))
          +le = pq.and_tf(H, z, pq.or_l(Bool.and(H, z), If.any_at(rest, q, d, 1n+R), top), eh)
          +ns = Equal.trans(Bool, Nat.is_lt(R, If.Rule.rank(s)), z, False{}, pq.lt_le(R, If.Rule.rank(s)), le)
          pq.post_go(rest, q, d, r, If.better(b, s), If.use.at(rest, q, d), {==}, pq.post_step(b, s, r, gb, ns), pq.or_r(Bool.and(H, z), If.any_at(rest, q, d, 1n+R), top))
        case False{}:
          +R = If.Rule.rank(r)
          +H = Bool.and(Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), d)), Nat.is_le(1n+R, If.Rule.rank(s)))
          pq.post_go(rest, q, d, r, b, If.use.at(rest, q, d), {==}, gb, pq.or_r(H, If.any_at(rest, q, d, 1n+R), top))

def pq.at_r_go(+k: Nat, +v: Nat, +r: If.Rule, c: Bool, ec: {Nat.is_lt(k, If.Rule.rank(r)) == c : Bool}, pb: {pq.pre_ok(Some{If.Best{k, v}}, r) == True{} : Bool}) -> {pq.good(If.better.at(c, If.Best{k, v}, r), r) == True{} : Bool}:
  match c:
    case True{}:
      pq.good_fresh(r)
    case False{}:
      pq.or_fl(Nat.is_lt(k, If.Rule.rank(r)), Bool.and(Nat.is_eq(k, If.Rule.rank(r)), Nat.is_eq(v, If.Rule.val(r))), pb, ec)

# at r: the best becomes r's rank and value
def pq.at_r(b: Maybe<&2, If.Best>, +r: If.Rule, pb: {pq.pre_ok(b, r) == True{} : Bool}) -> {pq.good(If.better(b, r), r) == True{} : Bool}:
  match b:
    case None{}:
      pq.good_fresh(r)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          pq.at_r_go(k, v, r, Nat.is_lt(k, If.Rule.rank(r)), {==}, pb)

# a rule s before r that applies keeps the best within r
def pq.fresh_ok(+s: If.Rule, +r: If.Rule, +q: If.Query, c: Bool, +ec: {Nat.is_lt(If.Rule.rank(s), If.Rule.rank(r)) == c : Bool}, hs: {Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), If.Rule.dir(r))) == True{} : Bool}, hr: {Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), If.Rule.dir(r))) == True{} : Bool}, nc: {If.clash(s, r) == False{} : Bool}, ts: {Nat.is_lt(If.Rule.rank(r), If.Rule.rank(s)) == False{} : Bool}) -> {pq.pre_ok(Some{If.Best{If.Rule.rank(s), If.Rule.val(s)}}, r) == True{} : Bool}:
  match c:
    case True{}:
      +RS = If.Rule.rank(s)
      +R = If.Rule.rank(r)
      %Equal.sym(Bool, Nat.is_lt(RS, R), True{}, ec) : {Bool.or(_, Bool.and(Nat.is_eq(RS, R), Nat.is_eq(If.Rule.val(s), If.Rule.val(r)))) == True{} : Bool}
      {==}
    case False{}:
      +RS = If.Rule.rank(s)
      +R = If.Rule.rank(r)
      +VS = If.Rule.val(s)
      +V = If.Rule.val(r)
      +er = pq.tri(RS, R, ts, ec)
      +ev = pq.same_val(q, s, r, If.Rule.dir(r), nc, hs, hr, er)
      %Equal.sym(Bool, Nat.is_lt(RS, R), False{}, ec) : {Bool.or(_, Bool.and(Nat.is_eq(RS, R), Nat.is_eq(VS, V))) == True{} : Bool}
      pq.and_t(Nat.is_eq(RS, R), Nat.is_eq(VS, V), er, pq.eq_of(VS, V, ev))

def pq.pre_at(+k: Nat, +v: Nat, +s: If.Rule, +r: If.Rule, +q: If.Query, c: Bool, pb: {pq.pre_ok(Some{If.Best{k, v}}, r) == True{} : Bool}, hs: {Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), If.Rule.dir(r))) == True{} : Bool}, hr: {Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), If.Rule.dir(r))) == True{} : Bool}, nc: {If.clash(s, r) == False{} : Bool}, ts: {Nat.is_lt(If.Rule.rank(r), If.Rule.rank(s)) == False{} : Bool}) -> {pq.pre_ok(If.better.at(c, If.Best{k, v}, s), r) == True{} : Bool}:
  match c:
    case True{}:
      pq.fresh_ok(s, r, q, Nat.is_lt(If.Rule.rank(s), If.Rule.rank(r)), {==}, hs, hr, nc, ts)
    case False{}:
      pb

def pq.pre_step(b: Maybe<&2, If.Best>, +s: If.Rule, +r: If.Rule, +q: If.Query, pb: {pq.pre_ok(b, r) == True{} : Bool}, hs: {Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), If.Rule.dir(r))) == True{} : Bool}, hr: {Bool.and(If.applies(q, r), Nat.is_eq(If.Rule.dir(r), If.Rule.dir(r))) == True{} : Bool}, nc: {If.clash(s, r) == False{} : Bool}, ts: {Nat.is_lt(If.Rule.rank(r), If.Rule.rank(s)) == False{} : Bool}) -> {pq.pre_ok(If.better(b, s), r) == True{} : Bool}:
  match b:
    case None{}:
      pq.fresh_ok(s, r, q, Nat.is_lt(If.Rule.rank(s), If.Rule.rank(r)), {==}, hs, hr, nc, ts)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          pq.pre_at(k, v, s, r, q, Nat.is_lt(k, If.Rule.rank(s)), pb, hs, hr, nc, ts)

def pq.clashes_mem(+s: If.Rule, t: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, h: {If.clashes(s, List.append(&2, If.Rule, t, r <> post)) == False{} : Bool}) -> {If.clash(s, r) == False{} : Bool}:
  match t:
    case Nil{}:
      pq.or_l(If.clash(s, r), If.clashes(s, post), h)
    case +u <> +t2:
      pq.clashes_mem(s, t2, r, post, pq.or_r(If.clash(s, u), If.clashes(s, List.append(&2, If.Rule, t2, r <> post)), h))

def pq.pre_go(pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, +b: Maybe<&2, If.Best>, hit: Bool, +eh: {If.use.at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r)) == hit : Bool}, pb: {pq.pre_ok(b, r) == True{} : Bool}, +top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}, +am: {If.ambiguous(List.append(&2, If.Rule, pre, r <> post)) == False{} : Bool}, +hr: {If.applies(q, r) == True{} : Bool}) -> {pq.good(If.look.go(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), b, hit), r) == True{} : Bool}:
  match pre:
    case Nil{}:
      match hit:
        case True{}:
          +D = If.Rule.dir(r)
          +R = If.Rule.rank(r)
          +H = Bool.and(Bool.and(If.applies(q, r), Nat.is_eq(D, D)), Nat.is_le(1n+R, R))
          pq.post_go(post, q, D, r, If.better(b, r), If.use.at(post, q, D), {==}, pq.at_r(b, r, pb), pq.or_r(H, If.any_at(post, q, D, 1n+R), top))
        case False{}:
          +D = If.Rule.dir(r)
          +hr2 = pq.and_t(If.applies(q, r), Nat.is_eq(D, D), hr, Equal.sym(Bool, True{}, Nat.is_eq(D, D), pq.eq_refl(D)))
          pq.flip({pq.good(If.look.go(r <> post, q, D, b, False{}), r) == True{} : Bool}, Bool.and(If.applies(q, r), Nat.is_eq(D, D)), hr2, eh)
    case +s <> +t:
      match hit:
        case True{}:
          +D = If.Rule.dir(r)
          +R = If.Rule.rank(r)
          +RS = If.Rule.rank(s)
          +X = List.append(&2, If.Rule, t, r <> post)
          +H = Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), D))
          +z = Nat.is_le(1n+R, RS)
          +le = pq.and_tf(H, z, pq.or_l(Bool.and(H, z), If.any_at(X, q, D, 1n+R), top), eh)
          +ts = Equal.trans(Bool, Nat.is_lt(R, RS), z, False{}, pq.lt_le(R, RS), le)
          +nc = pq.clashes_mem(s, t, r, post, pq.or_l(If.clashes(s, X), If.ambiguous(X), am))
          +hr2 = pq.and_t(If.applies(q, r), Nat.is_eq(D, D), hr, Equal.sym(Bool, True{}, Nat.is_eq(D, D), pq.eq_refl(D)))
          +pb2 = pq.pre_step(b, s, r, q, pb, eh, hr2, nc, ts)
          pq.pre_go(t, r, post, q, If.better(b, s), If.use.at(X, q, D), {==}, pb2, pq.or_r(Bool.and(H, z), If.any_at(X, q, D, 1n+R), top), pq.or_r(If.clashes(s, X), If.ambiguous(X), am), hr)
        case False{}:
          +D = If.Rule.dir(r)
          +R = If.Rule.rank(r)
          +X = List.append(&2, If.Rule, t, r <> post)
          +H = Bool.and(Bool.and(If.applies(q, s), Nat.is_eq(If.Rule.dir(s), D)), Nat.is_le(1n+R, If.Rule.rank(s)))
          pq.pre_go(t, r, post, q, b, If.use.at(X, q, D), {==}, pb, pq.or_r(H, If.any_at(X, q, D, 1n+R), top), pq.or_r(If.clashes(s, X), If.ambiguous(X), am), hr)

def pq.quirk_highest_wins(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, ok: {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == True{} : Bool}, hit: {If.applies(q, r) == True{} : Bool}, top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}) -> {If.lookup(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r)) == If.Known{If.Rule.val(r)} : If.Ans}:
  +L = List.append(&2, If.Rule, pre, r <> post)
  +D = If.Rule.dir(r)
  +am = pq.not_f(If.ambiguous(L), L.pq.and_r(If.known_all(L, known), Bool.not(If.ambiguous(L)), ok))
  +g = pq.pre_go(pre, r, post, q, None{}, If.use.at(L, q, D), {==}, {==}, top, am, hit)
  pq.good_ans(If.look.go(L, q, D, None{}, If.use.at(L, q, D)), r, g)

# the loose ids a plan lists, else none
def w2.listed(p: If.Plan) -> List<&2, Nat>:
  match p:
    case If.Fits{ls}:
      ls
    case If.Over{i}:
      Nil{}

def w2.over(p: If.Plan) -> Bool:
  match p:
    case If.Fits{ls}:
      False{}
    case If.Over{i}:
      True{}

def w2.ids(+ts: List<&2, If.Tool>) -> {If.ids(ts) == Laws.strict.ids(ts) : List<&2, Nat>}:
  match ts:
    case Nil{}:
      {==}
    case t <> rest:
      %w2.ids(rest) : {If.Tool.id(t) <> If.ids(rest) == If.Tool.id(t) <> _ : List<&2, Nat>}
      {==}

# plan.of with None lists ids(L); with Some it is Over
def w2.of_fits(m: Maybe<&2, Nat>, +L: List<&2, If.Tool>, +ls: List<&2, Nat>, f: {If.plan.of(m, L) == If.Fits{ls} : If.Plan}) -> {ls == If.ids(L) : List<&2, Nat>}:
  match m:
    case None{}:
      Equal.cong(If.Plan, List<&2, Nat>, w2.listed, If.Fits{ls}, If.Fits{If.ids(L)}, Equal.sym(If.Plan, If.Fits{If.ids(L)}, If.Fits{ls}, f))
    case Some{i}:
      L.pq.absurd({ls == If.ids(L) : List<&2, Nat>}, Equal.cong(If.Plan, Bool, w2.over, If.Over{i}, If.Fits{ls}, f))

def w2.mt(-A: Type, -x: Nat, e: {Some{x} == None{} : Maybe<&2, Nat>}) -> A:
  L.pq.absurd(A, Equal.cong(Maybe<&2, Nat>, Bool, m => Maybe.is_some(&2, Nat, m), Some{x}, None{}, e))

# is_eq(a, b) true and is_eq(a, c) false: b is not c
def w2.elem_at(+need: List<&2, Nat>, +a: Nat, +i: Nat, ai: {a == i : Nat}, n: {If.elem(need, i) == True{} : Bool}) -> {If.elem(need, a) == True{} : Bool}:
  %Equal.sym(Nat, a, i, ai) : {If.elem(need, _) == True{} : Bool}
  n

# a list of Nats that fits reads back (Laws.wire_list_round_trip, turned around)
def pc.nats(+xs: List<&2, Nat>, +rest: String, h: {Bool.and(Laws.wire_fits(List.length(&2, Nat, xs)), Laws.wire_nats_fit(xs)) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)) : Wr.Dec<List<&2, Nat>>}:
  Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)), Wr.Got{xs, rest}, Laws.wire_list_round_trip(xs, rest, h))

# a Maybe<Nat> that fits reads back (the same codec in ffi_infer and ffi_facts)

def pc.i_mnat(+m: Maybe<&2, Nat>, +rest: String, h: {Laws.core_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FIn.get_mnat(FIn.put_mnat(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %L.pc.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == FIn.get_mnat.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# (infer)
# -------

# the seq of FIn reads back a then b (the two decoders in turn)
def pc.seqFIn(~A: Data, ~B: Data, ~get: String -> Wr.Dec<B>, +a: A, +r: String, +b: B, +r2: String, d: Wr.Dec<A>,
  h1: {Wr.Got{a, r} == d : Wr.Dec<A>}, h2: {Wr.Got{b, r2} == get(r) : Wr.Dec<B>}) ->
  {Wr.Got{FIn.P2{a, b}, r2} == FIn.seq(~A, ~B, ~get, d) : Wr.Dec<FIn.P2<A, B>>}:
  %h1 : {Wr.Got{FIn.P2{a, b}, r2} == FIn.seq(~A, ~B, ~get, _) : Wr.Dec<FIn.P2<A, B>>}
  %h2 : {Wr.Got{FIn.P2{a, b}, r2} == FIn.seq.fin(~A, ~B, a, _) : Wr.Dec<FIn.P2<A, B>>}
  {==}

# a tool that fits reads back
def pc.i_tool(+t: If.Tool, +rest: String, h: {Laws.core_tool_fits(t) == True{} : Bool}) -> {Wr.Got{t, rest} == FIn.get_tool(FIn.put_tool(t, rest)) : Wr.Dec<If.Tool>}:
  match t:
    case If.Tool{+i, +p}:
      +hhh = h
      +hh0 = L.wr_and_r(Laws.wire_fits(i), Laws.wire_fits(p), hhh)
      +r1 = Wr.put_nat(p, rest)
      +r0 = Wr.put_nat(i, r1)
      +d0 = Wr.get_nat(r0)
      +e0 = L.pc.nat(i, r1, L.wr_and_l(Laws.wire_fits(i), Laws.wire_fits(p), hhh))
      +d1 = FIn.seq(~Nat, ~Nat, ~Wr.get_nat, d0)
      +e1 = pc.seqFIn(~Nat, ~Nat, ~Wr.get_nat, i, r1, p, rest, d0, e0, L.pc.nat(p, rest, hh0))
      %e1 : {Wr.Got{If.Tool{i, p}, rest} == FIn.get_tool.of(_) : Wr.Dec<If.Tool>}
      {==}

# the items of xs, then rest (If.Tool)
def pc.i_tool_items(xs: List<&2, If.Tool>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FIn.put_tool(x, pc.i_tool_items(t, rest))

def pc.i_tool_put_go(xs: List<&2, If.Tool>, -rest: String) ->
  {Wr.put_list.go(~If.Tool, ~FIn.put_tool, xs, rest) == (List.length(&2, If.Tool, xs), pc.i_tool_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~If.Tool, ~FIn.put_tool, t, rest), (List.length(&2, If.Tool, t), pc.i_tool_items(t, rest)), pc.i_tool_put_go(t, rest)) : {Wr.put_list.step(~If.Tool, ~FIn.put_tool, x, _) == (1n+List.length(&2, If.Tool, t), FIn.put_tool(x, pc.i_tool_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def pc.i_tool_put(+xs: List<&2, If.Tool>, -rest: String) ->
  {Wr.put_list(~If.Tool, ~FIn.put_tool, xs, rest) == Wr.put_nat(List.length(&2, If.Tool, xs), pc.i_tool_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~If.Tool, ~FIn.put_tool, xs, rest), (List.length(&2, If.Tool, xs), pc.i_tool_items(xs, rest)), pc.i_tool_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, If.Tool, xs), pc.i_tool_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def pc.i_tool_go_rt(+t: List<&2, If.Tool>, +x: If.Tool, +rest: String,
  +hf: {Laws.core_tools_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~If.Tool, ~FIn.get_tool, List.length(&2, If.Tool, t), FIn.get_tool(FIn.put_tool(x, pc.i_tool_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, If.Tool>>}:
  match t:
    case Nil{}:
      %pc.i_tool(x, rest, L.wr_and_l(Laws.core_tool_fits(x), True{}, hf)) : {Wr.get_list.go(~If.Tool, ~FIn.get_tool, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, If.Tool>>}
      {==}
    case Con{+y, +u}:
      %pc.i_tool(x, FIn.put_tool(y, pc.i_tool_items(u, rest)), L.wr_and_l(Laws.core_tool_fits(x), Laws.core_tools_fit(y <> u), hf)) : {Wr.get_list.go(~If.Tool, ~FIn.get_tool, 1n+List.length(&2, If.Tool, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, If.Tool>>}
      %Equal.sym(Wr.Dec<List<&2, If.Tool>>, Wr.get_list.go(~If.Tool, ~FIn.get_tool, List.length(&2, If.Tool, u), FIn.get_tool(FIn.put_tool(y, pc.i_tool_items(u, rest)))), Wr.Got{y <> u, rest}, pc.i_tool_go_rt(u, y, rest, L.wr_and_r(Laws.core_tool_fits(x), Laws.core_tools_fit(y <> u), hf))) : {Wr.get_list.cons(If.Tool, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, If.Tool>>}
      {==}

# a list that fits, of a length that fits, reads back
def pc.i_tools(+xs: List<&2, If.Tool>, +rest: String, h: {Bool.and(Laws.wire_fits(List.length(&2, If.Tool, xs)), Laws.core_tools_fit(xs)) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~If.Tool, ~FIn.get_tool, Wr.put_list(~If.Tool, ~FIn.put_tool, xs, rest)) : Wr.Dec<List<&2, If.Tool>>}:
  match xs:
    case Nil{}:
      %L.pc.nat(0n, rest, L.wr_and_l(Laws.wire_fits(0n), True{}, h)) : {Wr.Got{Nil{}, rest} == Wr.get_list.start(~If.Tool, ~FIn.get_tool, _) : Wr.Dec<List<&2, If.Tool>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~If.Tool, ~FIn.put_tool, x <> t, r), Wr.put_nat(List.length(&2, If.Tool, x <> t), pc.i_tool_items(x <> t, r)), pc.i_tool_put(x <> t, r)) : {Wr.Got{x <> t, r} == Wr.get_list(~If.Tool, ~FIn.get_tool, _) : Wr.Dec<List<&2, If.Tool>>}
      %L.pc.nat(List.length(&2, If.Tool, x <> t), pc.i_tool_items(x <> t, r), L.wr_and_l(Laws.wire_fits(List.length(&2, If.Tool, x <> t)), Laws.core_tools_fit(x <> t), hh)) : {Wr.Got{x <> t, r} == Wr.get_list.start(~If.Tool, ~FIn.get_tool, _) : Wr.Dec<List<&2, If.Tool>>}
      Equal.sym(Wr.Dec<List<&2, If.Tool>>, Wr.get_list.go(~If.Tool, ~FIn.get_tool, List.length(&2, If.Tool, t), FIn.get_tool(FIn.put_tool(x, pc.i_tool_items(t, r)))), Wr.Got{x <> t, r}, pc.i_tool_go_rt(t, x, r, L.wr_and_r(Laws.wire_fits(List.length(&2, If.Tool, x <> t)), Laws.core_tools_fit(x <> t), hh)))

# a strict plan request that fits reads back
def pc.i_req(+q: FIn.Req, +rest: String, h: {Laws.core_infer_fits(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FIn.get_req(FIn.put_req(q, rest)) : Wr.Dec<FIn.Req>}:
  match q:
    case FIn.Req{+cap, +ts, +need}:
      +hhh = h
      +hh0 = L.wr_and_r(Laws.core_mfits(cap), Bool.and(Bool.and(Laws.wire_fits(List.length(&2, If.Tool, ts)), Laws.core_tools_fit(ts)), Bool.and(Laws.wire_fits(List.length(&2, Nat, need)), Laws.wire_nats_fit(need))), hhh)
      +hh1 = L.wr_and_r(Bool.and(Laws.wire_fits(List.length(&2, If.Tool, ts)), Laws.core_tools_fit(ts)), Bool.and(Laws.wire_fits(List.length(&2, Nat, need)), Laws.wire_nats_fit(need)), hh0)
      +r2 = Wr.put_list(~Nat, ~Wr.put_nat, need, rest)
      +r1 = Wr.put_list(~If.Tool, ~FIn.put_tool, ts, r2)
      +r0 = FIn.put_mnat(cap, r1)
      +d0 = FIn.get_mnat(r0)
      +e0 = pc.i_mnat(cap, r1, L.wr_and_l(Laws.core_mfits(cap), Bool.and(Bool.and(Laws.wire_fits(List.length(&2, If.Tool, ts)), Laws.core_tools_fit(ts)), Bool.and(Laws.wire_fits(List.length(&2, Nat, need)), Laws.wire_nats_fit(need))), hhh))
      +d1 = FIn.seq(~Maybe<&2, Nat>, ~List<&2, If.Tool>, ~FIn.get_tools, d0)
      +e1 = pc.seqFIn(~Maybe<&2, Nat>, ~List<&2, If.Tool>, ~FIn.get_tools, cap, r1, ts, r2, d0, e0, pc.i_tools(ts, r2, L.wr_and_l(Bool.and(Laws.wire_fits(List.length(&2, If.Tool, ts)), Laws.core_tools_fit(ts)), Bool.and(Laws.wire_fits(List.length(&2, Nat, need)), Laws.wire_nats_fit(need)), hh0)))
      +d2 = FIn.seq(~FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, ~List<&2, Nat>, ~FIn.get_ids, d1)
      +e2 = pc.seqFIn(~FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, ~List<&2, Nat>, ~FIn.get_ids, FIn.P2{cap, ts}, r2, need, rest, d1, e1, pc.nats(need, rest, hh1))
      %e2 : {Wr.Got{FIn.Req{cap, ts, need}, rest} == FIn.get_req.of(_) : Wr.Dec<FIn.Req>}
      {==}
