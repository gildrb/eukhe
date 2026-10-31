# eukhe: lemmas of the plan proofs of area rlm_query: the code's steps are
# the spec's (qp.*: the waves follow Nat.divmod's loop), what an admitted
# plan is (qp.admitted), and the spec's waves (qw.*: each holds a call and
# at most k, and they add up to the batch)

import Base
import ../../../bend/rlm_query.bend as Rq
import ../../../spec/rlm/query.bend as QSpec
import ../../../laws/rlm_query.bend as RlmQuery
import ./nat.bend as LN

# Logic
# -----

def qw.and(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def qw.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def qw.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LN.rq.absurd({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def qp.If(p: Rq.Plan, G: Type) -> Type:
  match p:
    case Rq.Waves{ws}:
      G
    case Rq.Refused{f}:
      Unit

# a refusal is no admission
def qp.absurd(-G: Type, -f: Rq.Refusal, -ws: List<&2, Nat>, e: {Rq.Refused{f} == Rq.Waves{ws} : Rq.Plan}) -> G:
  %e : qp.If(_, G)
  Unit{}

def qp.ws_of(p: Rq.Plan) -> List<&2, Nat>:
  match p:
    case Rq.Waves{ws}:
      ws
    case Rq.Refused{f}:
      Nil{}

# The code's steps are the spec's
# -------------------------------

def qp.total.go(xs: List<&2, Nat>, +acc: Nat) -> {Rq.total.go(xs, acc) == Nat.add(acc, QSpec.total(xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(acc, 0n), acc, LN.rq.add_zero(acc))
    case Con{+x, +t}:
      Equal.trans(Nat, Rq.total.go(t, Nat.add(acc, x)), Nat.add(Nat.add(acc, x), QSpec.total(t)), Nat.add(acc, Nat.add(x, QSpec.total(t))), qp.total.go(t, Nat.add(acc, x)), LN.rq.add_assoc(acc, x, QSpec.total(t)))

# the batch's bytes are the spec's
def qp.total(+xs: List<&2, Nat>) -> {Rq.total(xs) == QSpec.total(xs) : Nat}:
  qp.total.go(xs, 0n)

def qp.over(b: Nat, +u: Nat, +t: Nat) -> {Rq.over(b, u, t) == QSpec.over_budget(b, u, t) : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+k:
      {==}

def qp.width.succ(x: Bool, +p: Nat, +q: Nat) -> {Rq.width.of(x, 1n+p, 1n+q) == 1n+Rq.width.of(x, p, q) : Nat}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def qp.min(a: Nat, b: Nat) -> {Rq.width.of(Nat.is_le(a, b), a, b) == Nat.min(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      Equal.trans(Nat, Rq.width.of(Nat.is_le(p, q), 1n+p, 1n+q), 1n+Rq.width.of(Nat.is_le(p, q), p, q), 1n+Nat.min(p, q), qp.width.succ(Nat.is_le(p, q), p, q), Equal.cong(Nat, Nat, z => 1n+z, Rq.width.of(Nat.is_le(p, q), p, q), Nat.min(p, q), qp.min(p, q)))

# a wave's calls are the spec's
def qp.width(w: Nat, +room: Nat) -> {Rq.width(w, room) == QSpec.wave(w, room) : Nat}:
  match w:
    case 0n:
      {==}
    case 1n++p:
      qp.min(1n+p, room)

def qp.last(r: Nat) -> {Rq.waves.last(r) == QSpec.rest(r) : List<&2, Nat>}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      {==}

# k after d copies of k is one copy more
def qp.snoc(d: Nat, +k: Nat, +xs: List<&2, Nat>) -> {List.append(&2, Nat, QSpec.copies(d, k), k <> xs) == k <> List.append(&2, Nat, QSpec.copies(d, k), xs) : List<&2, Nat>}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => k <> z, List.append(&2, Nat, QSpec.copies(p, k), k <> xs), k <> List.append(&2, Nat, QSpec.copies(p, k), xs), qp.snoc(p, k, xs))

# the code's loop is Nat.divmod's: d waves done, r calls in the open wave,
# m more fit in it
def qp.go(n: Nat, m: Nat, +r: Nat, +d: Nat, +bp: Nat, +eq: {Nat.add(m, r) == bp : Nat}) -> {List.append(&2, Nat, QSpec.copies(d, 1n+bp), Rq.waves.go(n, m, r)) == List.append(&2, Nat, QSpec.copies(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp), QSpec.rest(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)))) : List<&2, Nat>}:
  match n:
    case 0n:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.append(&2, Nat, QSpec.copies(d, 1n+bp), z), Rq.waves.last(r), QSpec.rest(r), qp.last(r))
    case 1n++np:
      match m:
        case 0n:
          %Equal.sym(Nat, r, bp, eq) : {List.append(&2, Nat, QSpec.copies(d, 1n+bp), (1n+_) <> Rq.waves.go(np, r, 0n)) == List.append(&2, Nat, QSpec.copies(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), QSpec.rest(Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)))) : List<&2, Nat>}
          Equal.trans(List<&2, Nat>, List.append(&2, Nat, QSpec.copies(d, 1n+bp), (1n+bp) <> Rq.waves.go(np, r, 0n)), (1n+bp) <> List.append(&2, Nat, QSpec.copies(d, 1n+bp), Rq.waves.go(np, r, 0n)), List.append(&2, Nat, QSpec.copies(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), QSpec.rest(Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)))), qp.snoc(d, 1n+bp, Rq.waves.go(np, r, 0n)), qp.go(np, r, 0n, 1n+d, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, LN.rq.add_zero(r), eq)))
        case 1n++mp:
          qp.go(np, mp, 1n+r, d, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, LN.rq.add_succ(mp, r), eq))

# the waves are the spec's
def qp.waves(k: Nat, +n: Nat) -> {Rq.waves(n, k) == QSpec.waves(n, k) : List<&2, Nat>}:
  match k:
    case 0n:
      qp.last(n)
    case 1n++bp:
      qp.go(n, bp, 0n, 0n, bp, LN.rq.add_zero(bp))

def qp.full(f: Bool, +c: Nat, +r: Nat, +w: Nat, +n: Nat) -> {Rq.plan.full(f, c, r, w, n) == QSpec.plan.cap(f, c, r, w, n) : Rq.Plan}:
  match f:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, Rq.width(w, Nat.sub(c, r)), QSpec.wave(w, Nat.sub(c, r)), qp.width(w, Nat.sub(c, r))) : {Rq.Waves{Rq.waves(n, _)} == Rq.Waves{QSpec.waves(n, QSpec.wave(w, Nat.sub(c, r)))} : Rq.Plan}
      Equal.cong(List<&2, Nat>, Rq.Plan, z => Rq.Waves{z}, Rq.waves(n, QSpec.wave(w, Nat.sub(c, r))), QSpec.waves(n, QSpec.wave(w, Nat.sub(c, r))), qp.waves(QSpec.wave(w, Nat.sub(c, r)), n))

def qp.budget(o: Bool, +r: Nat, +c: Nat, +w: Nat, +b: Nat, +u: Nat, +sizes: List<&2, Nat>) -> {Rq.plan.budget(o, r, c, w, b, u, QSpec.total(sizes), List.length(&2, Nat, sizes)) == QSpec.plan.of(o, r, c, w, b, u, sizes) : Rq.Plan}:
  match o:
    case True{}:
      {==}
    case False{}:
      qp.full(Nat.is_le(c, r), c, r, w, List.length(&2, Nat, sizes))

# the decision is the spec's
def qp.plan(+r: Nat, +c: Nat, +w: Nat, +b: Nat, +u: Nat, +sizes: List<&2, Nat>) -> {Rq.plan(r, c, w, b, u, sizes) == QSpec.plan(r, c, w, b, u, sizes) : Rq.Plan}:
  %Equal.sym(Nat, Rq.total(sizes), QSpec.total(sizes), qp.total(sizes)) : {Rq.plan.budget(Rq.over(b, u, _), r, c, w, b, u, _, List.length(&2, Nat, sizes)) == QSpec.plan(r, c, w, b, u, sizes) : Rq.Plan}
  %Equal.sym(Bool, Rq.over(b, u, QSpec.total(sizes)), QSpec.over_budget(b, u, QSpec.total(sizes)), qp.over(b, u, QSpec.total(sizes))) : {Rq.plan.budget(_, r, c, w, b, u, QSpec.total(sizes), List.length(&2, Nat, sizes)) == QSpec.plan(r, c, w, b, u, sizes) : Rq.Plan}
  qp.budget(QSpec.over_budget(b, u, QSpec.total(sizes)), r, c, w, b, u, sizes)

# What an admitted plan is
# ------------------------

def qp.adm.cap(f: Bool, +c: Nat, +r: Nat, +w: Nat, +n: Nat, +ws: List<&2, Nat>, hf: {Nat.is_le(c, r) == f : Bool}, e: {QSpec.plan.cap(f, c, r, w, n) == Rq.Waves{ws} : Rq.Plan}) -> {ws == QSpec.waves(n, QSpec.wave(w, Nat.sub(c, r))) : List<&2, Nat>} & {Nat.is_lt(r, c) == True{} : Bool}:
  match f:
    case True{}:
      qp.absurd({ws == QSpec.waves(n, QSpec.wave(w, Nat.sub(c, r))) : List<&2, Nat>} & {Nat.is_lt(r, c) == True{} : Bool}, Rq.Full{c}, ws, e)
    case False{}:
      (Equal.sym(List<&2, Nat>, QSpec.waves(n, QSpec.wave(w, Nat.sub(c, r))), ws, Equal.cong(Rq.Plan, List<&2, Nat>, qp.ws_of, Rq.Waves{QSpec.waves(n, QSpec.wave(w, Nat.sub(c, r)))}, Rq.Waves{ws}, e)), LN.rq.nle_lt(c, r, hf))

def qp.adm.of(o: Bool, +r: Nat, +c: Nat, +w: Nat, +b: Nat, +u: Nat, +sizes: List<&2, Nat>, +ws: List<&2, Nat>, e: {QSpec.plan.of(o, r, c, w, b, u, sizes) == Rq.Waves{ws} : Rq.Plan}) -> {ws == QSpec.waves(List.length(&2, Nat, sizes), QSpec.wave(w, Nat.sub(c, r))) : List<&2, Nat>} & {Nat.is_lt(r, c) == True{} : Bool}:
  match o:
    case True{}:
      qp.absurd({ws == QSpec.waves(List.length(&2, Nat, sizes), QSpec.wave(w, Nat.sub(c, r))) : List<&2, Nat>} & {Nat.is_lt(r, c) == True{} : Bool}, Rq.OverBudget{QSpec.total(sizes), Nat.sub(b, u), b}, ws, e)
    case False{}:
      qp.adm.cap(Nat.is_le(c, r), c, r, w, List.length(&2, Nat, sizes), ws, {==}, e)

# an admitted batch: the spec's waves, with r below the cap
def qp.admitted(+r: Nat, +c: Nat, +w: Nat, +b: Nat, +u: Nat, +sizes: List<&2, Nat>, +ws: List<&2, Nat>, e: {Rq.plan(r, c, w, b, u, sizes) == Rq.Waves{ws} : Rq.Plan}) -> {ws == QSpec.waves(List.length(&2, Nat, sizes), QSpec.wave(w, Nat.sub(c, r))) : List<&2, Nat>} & {Nat.is_lt(r, c) == True{} : Bool}:
  qp.adm.of(QSpec.over_budget(b, u, QSpec.total(sizes)), r, c, w, b, u, sizes, ws, Equal.trans(Rq.Plan, QSpec.plan(r, c, w, b, u, sizes), Rq.plan(r, c, w, b, u, sizes), Rq.Waves{ws}, Equal.sym(Rq.Plan, Rq.plan(r, c, w, b, u, sizes), QSpec.plan(r, c, w, b, u, sizes), qp.plan(r, c, w, b, u, sizes)), e))

# a budget not passed
def qp.within(b: Nat, +u: Nat, +t: Nat, h: {Bool.or(Nat.is_eq(b, 0n), Nat.is_le(Nat.add(u, t), b)) == True{} : Bool}) -> {QSpec.over_budget(b, u, t) == False{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n++k:
      LN.rq.le_not_lt(Nat.add(u, t), 1n+k, h)

# The spec's waves
# ----------------

# every wave holds a call and at most k
def qw.within(ws: List<&2, Nat>, +k: Nat) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, k)), qw.within(t, k))

def qw.cons(+x: Nat, +k: Nat, -t: List<&2, Nat>, hx: {Nat.is_lt(0n, x) == True{} : Bool}, hk: {Nat.is_le(x, k) == True{} : Bool}, ht: {qw.within(t, k) == True{} : Bool}) -> {qw.within(x <> t, k) == True{} : Bool}:
  qw.and(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, k)), qw.within(t, k), qw.and(Nat.is_lt(0n, x), Nat.is_le(x, k), hx, hk), ht)

def qw.go(n: Nat, m: Nat, +r: Nat, +bp: Nat, +eq: {Nat.add(m, r) == bp : Nat}) -> {qw.within(Rq.waves.go(n, m, r), 1n+bp) == True{} : Bool}:
  match n:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n++p:
          +le = Equal.trans(Bool, Nat.is_le(1n+p, bp), Nat.is_le(1n+p, Nat.add(m, 1n+p)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1n+p, z), bp, Nat.add(m, 1n+p), Equal.sym(Nat, Nat.add(m, 1n+p), bp, eq)), LN.rq.le_add(m, 1n+p))
          qw.cons(1n+p, 1n+bp, Nil{}, {==}, LN.rq.le_step(1n+p, bp, le), {==})
    case 1n++np:
      match m:
        case 0n:
          +le = Equal.trans(Bool, Nat.is_le(r, bp), Nat.is_le(r, r), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(r, z), bp, r, Equal.sym(Nat, r, bp, eq)), LN.rq.le_refl(r))
          qw.cons(1n+r, 1n+bp, Rq.waves.go(np, r, 0n), {==}, le, qw.go(np, r, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, LN.rq.add_zero(r), eq)))
        case 1n++mp:
          qw.go(np, mp, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, LN.rq.add_succ(mp, r), eq))

# waves of k > 0 each hold a call and at most k
def qw.waves(k: Nat, +n: Nat, pos: {Nat.is_lt(0n, k) == True{} : Bool}) -> {qw.within(QSpec.waves(n, k), k) == True{} : Bool}:
  match k:
    case 0n:
      LN.rq.absurd({qw.within(QSpec.waves(n, 0n), 0n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, pos))
    case 1n++bp:
      %qp.waves(1n+bp, n) : {qw.within(_, 1n+bp) == True{} : Bool}
      qw.go(n, bp, 0n, bp, LN.rq.add_zero(bp))

# a wave holds a call when there is room
def qw.k_pos(w: Nat, room: Nat, h: {Nat.is_lt(0n, room) == True{} : Bool}) -> {Nat.is_lt(0n, QSpec.wave(w, room)) == True{} : Bool}:
  match w room:
    case 0n _:
      h
    case 1n+p 0n:
      LN.rq.absurd({Nat.is_lt(0n, QSpec.wave(1n+p, 0n)) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      {==}

# a wave is at most the room
def qw.k_room(w: Nat, +room: Nat) -> {Nat.is_le(QSpec.wave(w, room), room) == True{} : Bool}:
  match w:
    case 0n:
      LN.rq.le_refl(room)
    case 1n++p:
      LN.rq.min_le_r(1n+p, room)

# a wave is at most a width given
def qw.k_width(+p: Nat, +room: Nat) -> {Nat.is_le(QSpec.wave(1n+p, room), 1n+p) == True{} : Bool}:
  LN.rq.min_le_l(1n+p, room)

# waves of at most k, k within the room under c: each wave fits the cap
def qw.capped(ws: List<&2, Nat>, +r: Nat, +c: Nat, +k: Nat, +hw: {qw.within(ws, k) == True{} : Bool}, +hk: {Nat.is_le(k, Nat.sub(c, r)) == True{} : Bool}, +hr: {Nat.is_le(r, c) == True{} : Bool}) -> {RlmQuery.rq_capped(r, c, ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = hw
      +hx = qw.and_l(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, k)), qw.within(t, k), h0)
      +ht = qw.and_r(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, k)), qw.within(t, k), h0)
      +h1 = qw.and_l(Nat.is_lt(0n, x), Nat.is_le(x, k), hx)
      +h2 = qw.and_r(Nat.is_lt(0n, x), Nat.is_le(x, k), hx)
      +hle = LN.rq.sub_add_le(r, c, x, LN.rq.le_trans(x, k, Nat.sub(c, r), h2, hk), hr)
      qw.and(Bool.and(Nat.is_lt(0n, x), Nat.is_le(Nat.add(r, x), c)), RlmQuery.rq_capped(r, c, t), qw.and(Nat.is_lt(0n, x), Nat.is_le(Nat.add(r, x), c), h1, hle), qw.capped(t, r, c, k, ht, hk, hr))

# waves of at most k, k at most w: each wave is at most w
def qw.narrow(ws: List<&2, Nat>, +w: Nat, +k: Nat, +hw: {qw.within(ws, k) == True{} : Bool}, +hk: {Nat.is_le(k, w) == True{} : Bool}) -> {RlmQuery.rq_narrow(w, ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = hw
      +hx = qw.and_l(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, k)), qw.within(t, k), h0)
      +ht = qw.and_r(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, k)), qw.within(t, k), h0)
      +h2 = qw.and_r(Nat.is_lt(0n, x), Nat.is_le(x, k), hx)
      qw.and(Nat.is_le(x, w), RlmQuery.rq_narrow(w, t), LN.rq.le_trans(x, k, w, h2, hk), qw.narrow(t, w, k, ht, hk))

def qw.sum_go(n: Nat, m: Nat, +r: Nat) -> {QSpec.total(Rq.waves.go(n, m, r)) == Nat.add(r, n) : Nat}:
  match n:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case 1n++np:
      match m:
        case 0n:
          Equal.trans(Nat, Nat.add(1n+r, QSpec.total(Rq.waves.go(np, r, 0n))), Nat.add(1n+r, np), Nat.add(r, 1n+np), Equal.cong(Nat, Nat, z => Nat.add(1n+r, z), QSpec.total(Rq.waves.go(np, r, 0n)), np, qw.sum_go(np, r, 0n)), Equal.sym(Nat, Nat.add(r, 1n+np), 1n+Nat.add(r, np), LN.rq.add_succ(r, np)))
        case 1n++mp:
          Equal.trans(Nat, QSpec.total(Rq.waves.go(np, mp, 1n+r)), Nat.add(1n+r, np), Nat.add(r, 1n+np), qw.sum_go(np, mp, 1n+r), Equal.sym(Nat, Nat.add(r, 1n+np), 1n+Nat.add(r, np), LN.rq.add_succ(r, np)))

# the waves add up to the batch
def qw.sum(k: Nat, +n: Nat) -> {QSpec.total(QSpec.waves(n, k)) == n : Nat}:
  match k:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n++p:
          LN.rq.add_zero(1n+p)
    case 1n++bp:
      %qp.waves(1n+bp, n) : {QSpec.total(_) == n : Nat}
      qw.sum_go(n, bp, 0n)
