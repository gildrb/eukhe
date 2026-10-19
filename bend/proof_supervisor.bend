# proof_supervisor: the D1 laws of laws/supervisor.bend.
#
# - restart_gives_up: the failures of a crash loop stay in the window, so
#   their count only grows (`ps.block`), up to the give-up.
# - timeouts_ordered: each timeout is a sum that contains the timeouts it
#   waits for.
# - revive_after_refresh: the time since the last record stays below the
#   refresh period (`ps.since_lt`), so a boot within the boot window
#   finds the evidence within the max age.
# - orphan_never_aborts_resumable: every exit is sound (`ps.exit_sound`)
#   and an exit is final.
# - idle_shutdown_never_aborts: a closed gate never holds a run
#   (`ps.Inv`), so a commit, which needs every gate closed, stops no run.
# - adopt_same_build: an adoption reads equal build numbers.

import Base
import ./supervise.bend as Su
import ./revive.bend as Rv
import ./orphan.bend as Or
import ./launcher.bend as La

# Logic
# -----

def ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ps.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : ps.BD(_, Unit, A)
  Unit{}

def ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ps.BD(_, A, Unit)
  Unit{}

def ps.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      ps.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

# Numbers
# -------

def ps.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      ps.le_refl(p)

def ps.le_zero(b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ps.le_succ(a: Nat) -> {Nat.is_le(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      ps.le_succ(p)

def ps.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      ps.le_zero(c)
    case 1n+p 0n _:
      ps.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      ps.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      ps.le_trans(p, q, r, ab, bc)

# a is at most a + b
def ps.le_add(a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      ps.le_zero(b)
    case 1n+p:
      ps.le_add(p, b)

# x is at most g + x
def ps.le_add_l(+g: Nat, +x: Nat) -> {Nat.is_le(x, Nat.add(g, x)) == True{} : Bool}:
  match g:
    case 0n:
      ps.le_refl(x)
    case 1n+p:
      ps.le_trans(x, Nat.add(p, x), 1n+Nat.add(p, x), ps.le_add_l(p, x), ps.le_succ(Nat.add(p, x)))

# adding g on the left keeps the order
def ps.le_mono(g: Nat, -a: Nat, -x: Nat, h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(Nat.add(g, a), Nat.add(g, x)) == True{} : Bool}:
  match g:
    case 0n:
      h
    case 1n+p:
      ps.le_mono(p, a, x, h)

# adding b on the right keeps the order
def ps.le_mono_r(a: Nat, h: Nat, +b: Nat, ah: {Nat.is_le(a, h) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(h, b)) == True{} : Bool}:
  match a h:
    case 0n _:
      ps.le_add_l(h, b)
    case 1n+p 0n:
      ps.absurdF({Nat.is_le(Nat.add(1n+p, b), Nat.add(0n, b)) == True{} : Bool}, ah)
    case 1n+p 1n+q:
      ps.le_mono_r(p, q, b, ah)

def ps.le_lt(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      ps.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, bc)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      ps.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      ps.absurdF({Nat.is_lt(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      ps.absurdF({Nat.is_lt(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      ps.le_lt(p, q, r, ab, bc)

def ps.lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      ps.le_zero(b)
    case 1n+p 0n:
      ps.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ps.lt_le(p, q, h)

# k + 1 at most n makes k below n
def ps.lt_of_le_succ(k: Nat, n: Nat, h: {Nat.is_le(1n+k, n) == True{} : Bool}) -> {Nat.is_lt(k, n) == True{} : Bool}:
  match k n:
    case 0n 0n:
      ps.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      ps.absurdF({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ps.lt_of_le_succ(p, q, h)

# r below h and r + 1 not h make r + 1 below h
def ps.lt_succ_ne(r: Nat, h: Nat, lt: {Nat.is_lt(r, h) == True{} : Bool}, ne: {Nat.is_eq(1n+r, h) == False{} : Bool}) -> {Nat.is_lt(1n+r, h) == True{} : Bool}:
  match r h:
    case 0n 0n:
      ps.absurdF({Nat.is_lt(1n, 0n) == True{} : Bool}, lt)
    case 0n 1n+q:
      match q:
        case 0n:
          ps.absurd({Nat.is_lt(1n, 1n) == True{} : Bool}, ne)
        case 1n+s:
          {==}
    case 1n+p 0n:
      ps.absurdF({Nat.is_lt(2n+p, 0n) == True{} : Bool}, lt)
    case 1n+p 1n+q:
      ps.lt_succ_ne(p, q, lt, ne)

def ps.add_succ_r(a: Nat, +m: Nat) -> {Nat.add(a, 1n+m) == 1n+Nat.add(a, m) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ps.add_succ_r(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

def ps.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ps.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def ps.eq_of_is_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ps.absurdF({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      ps.absurdF({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, ps.eq_of_is_eq(p, q, e))

# (D1) restart_gives_up
# ---------------------

# the ages of A at most x
def ps.young.put(b: Bool, r: Nat) -> Nat:
  match b:
    case True{}:
      1n+r
    case False{}:
      r

def ps.young(+x: Nat, A: List<&2, Nat>) -> Nat:
  match A:
    case Nil{}:
      0n
    case +a <> t:
      ps.young.put(Nat.is_le(a, x), ps.young(x, t))

def ps.put_ge(b: Bool, +r: Nat) -> {Nat.is_le(r, ps.young.put(b, r)) == True{} : Bool}:
  match b:
    case True{}:
      ps.le_succ(r)
    case False{}:
      ps.le_refl(r)

def ps.young_len.put(b: Bool, +r: Nat, +l: Nat, h: {Nat.is_le(r, l) == True{} : Bool}) -> {Nat.is_le(ps.young.put(b, r), 1n+l) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      ps.le_trans(r, l, 1n+l, h, ps.le_succ(l))

def ps.young_len(+x: Nat, A: List<&2, Nat>) -> {Nat.is_le(ps.young(x, A), List.length(&2, Nat, A)) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +t:
      ps.young_len.put(Nat.is_le(a, x), ps.young(x, t), List.length(&2, Nat, t), ps.young_len(x, t))

# the window keeps every young age g ms later: one age
def ps.keep.at(b1: Bool, +a: Nat, +x: Nat, +g: Nat, +w: Nat, e1: {Nat.is_le(a, x) == b1 : Bool}, b2: Bool, e2: {Nat.is_lt(Nat.add(g, a), w) == b2 : Bool}, lt: {Nat.is_lt(Nat.add(g, x), w) == True{} : Bool}, +y: Nat, +k: List<&2, Nat>, ih: {Nat.is_le(y, ps.young(Nat.add(g, x), k)) == True{} : Bool})
  -> {Nat.is_le(ps.young.put(b1, y), ps.young(Nat.add(g, x), Su.keep.put(b2, Nat.add(g, a), k))) == True{} : Bool}:
  match b1 b2:
    case True{} True{}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(g, a), Nat.add(g, x)), True{}, ps.le_mono(g, a, x, e1)) : {Nat.is_le(1n+y, ps.young.put(_, ps.young(Nat.add(g, x), k))) == True{} : Bool}
      ih
    case True{} False{}:
      ps.absurd({Nat.is_le(1n+y, ps.young(Nat.add(g, x), k)) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_lt(Nat.add(g, a), w), False{}, Equal.sym(Bool, Nat.is_lt(Nat.add(g, a), w), True{}, ps.le_lt(Nat.add(g, a), Nat.add(g, x), w, ps.le_mono(g, a, x, e1), lt)), e2))
    case False{} True{}:
      ps.le_trans(y, ps.young(Nat.add(g, x), k), ps.young.put(Nat.is_le(Nat.add(g, a), Nat.add(g, x)), ps.young(Nat.add(g, x), k)), ih, ps.put_ge(Nat.is_le(Nat.add(g, a), Nat.add(g, x)), ps.young(Nat.add(g, x), k)))
    case False{} False{}:
      ih

# the window keeps every young age g ms later
def ps.keep(+w: Nat, +g: Nat, +x: Nat, A: List<&2, Nat>, +lt: {Nat.is_lt(Nat.add(g, x), w) == True{} : Bool})
  -> {Nat.is_le(ps.young(x, A), ps.young(Nat.add(g, x), Su.keep(w, Su.older(g, A)))) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +t:
      ps.keep.at(Nat.is_le(a, x), a, x, g, w, {==}, Nat.is_lt(Nat.add(g, a), w), {==}, lt, ps.young(x, t), Su.keep(w, Su.older(g, t)), ps.keep(w, g, x, t, lt))

# the span from c is at least c
def ps.span_ge(gs: List<&2, Nat>, +c: Nat) -> {Nat.is_le(c, Su.span.go(gs, c)) == True{} : Bool}:
  match gs:
    case Nil{}:
      ps.le_refl(c)
    case +g <> +rest:
      ps.le_trans(c, Nat.add(g, c), Su.span.go(rest, Nat.add(g, c)), ps.le_add_l(g, c), ps.span_ge(rest, Nat.add(g, c)))

# a new failure is young
def ps.young_new(+z: Nat, +k: List<&2, Nat>) -> {ps.young(z, 0n <> k) == 1n+ps.young(z, k) : Nat}:
  %Equal.sym(Bool, Nat.is_le(0n, z), True{}, ps.le_zero(z)) : {ps.young.put(_, ps.young(z, k)) == 1n+ps.young(z, k) : Nat}
  {==}

def ps.block.yo(+z: Nat, +k: List<&2, Nat>, +m: Nat, kept: {Nat.is_le(m, ps.young(z, k)) == True{} : Bool}) -> {Nat.is_le(1n+m, ps.young(z, 0n <> k)) == True{} : Bool}:
  %Equal.sym(Nat, ps.young(z, 0n <> k), 1n+ps.young(z, k), ps.young_new(z, k)) : {Nat.is_le(1n+m, _) == True{} : Bool}
  kept

# from a state with m failures at most x ms old (and n at least m), the
# failures gs inside the window leave at least m + |gs| in the window
def ps.block(+c: Su.Cfg, gs: List<&2, Nat>, s: Su.St, +x: Nat, +m: Nat,
  yo: {Nat.is_le(m, ps.young(x, Su.St.ages(s))) == True{} : Bool},
  nm: {Nat.is_le(m, Su.St.n(s)) == True{} : Bool},
  +sp: {Nat.is_lt(Su.span.go(gs, x), Su.Cfg.w(c)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(List.length(&2, Nat, gs), m), Su.St.n(Su.go(c, gs, s))) == True{} : Bool}:
  match gs:
    case Nil{}:
      nm
    case +g <> +rest:
      match s:
        case Su.St{+a, n}:
          +w = Su.Cfg.w(c)
          +z = Nat.add(g, x)
          +k = Su.kept(c, g, a)
          +lt = ps.le_lt(z, Su.span.go(rest, z), w, ps.span_ge(rest, z), sp)
          +kept = ps.le_trans(m, ps.young(x, a), ps.young(z, k), yo, ps.keep(w, g, x, a, lt))
          +yo2 = ps.block.yo(z, k, m, kept)
          +nm2 = ps.le_trans(m, ps.young(z, k), List.length(&2, Nat, k), kept, ps.young_len(z, k))
          %ps.add_succ_r(List.length(&2, Nat, rest), m) : {Nat.is_le(_, Su.St.n(Su.go(c, rest, Su.St{0n <> k, 1n+List.length(&2, Nat, k)}))) == True{} : Bool}
          ps.block(c, rest, Su.St{0n <> k, 1n+List.length(&2, Nat, k)}, z, 1n+m, yo2, nm2, sp)

# the first failure of the loop is young
def ps.first_young(+c: Su.Cfg, s: Su.St, +g: Nat) -> {Nat.is_le(1n, ps.young(0n, Su.St.ages(Su.step(c, s, g)))) == True{} : Bool}:
  match s:
    case Su.St{a, n}:
      ps.le_zero(ps.young(0n, Su.kept(c, g, a)))

# and counted
def ps.first_n(+c: Su.Cfg, s: Su.St, +g: Nat) -> {Nat.is_le(1n, Su.St.n(Su.step(c, s, g))) == True{} : Bool}:
  match s:
    case Su.St{a, n}:
      ps.le_zero(List.length(&2, Nat, Su.kept(c, g, a)))

def ps.go_append(+c: Su.Cfg, xs: List<&2, Nat>, +ys: List<&2, Nat>, s: Su.St) -> {Su.go(c, List.append(&2, Nat, xs, ys), s) == Su.go(c, ys, Su.go(c, xs, s)) : Su.St}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      ps.go_append(c, rest, ys, Su.step(c, s, x))

def ps.gives_up_of(+c: Su.Cfg, +n: Nat, lt: {Nat.is_lt(Su.Cfg.k(c), n) == True{} : Bool}) -> {Su.gives_up(Su.verdict(c, n)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(Su.Cfg.k(c), n), True{}, lt) : {Su.gives_up(Su.verdict.put(_, c, n)) == True{} : Bool}
  {==}

def ps.le_k(+l: Nat, +k: Nat, +n: Nat, many: {l == k : Nat}, blk: {Nat.is_le(Nat.add(l, 1n), n) == True{} : Bool}) -> {Nat.is_le(1n+k, n) == True{} : Bool}:
  %many : {Nat.is_le(1n+_, n) == True{} : Bool}
  %ps.add_zero(l) : {Nat.is_le(1n+_, n) == True{} : Bool}
  %ps.add_succ_r(l, 0n) : {Nat.is_le(_, n) == True{} : Bool}
  blk

def ps.restart_gives_up(+c: Su.Cfg, +pre: List<&2, Nat>, +g: Nat, +gs: List<&2, Nat>, many: {List.length(&2, Nat, gs) == Su.Cfg.k(c) : Nat}, fast: {Nat.is_lt(Su.span(gs), Su.Cfg.w(c)) == True{} : Bool})
  -> {Su.gives_up(Su.verdict(c, Su.failures(c, List.append(&2, Nat, pre, g <> gs)))) == True{} : Bool}:
  +s0 = Su.go(c, pre, Su.St.empty())
  +s1 = Su.step(c, s0, g)
  +blk = ps.block(c, gs, s1, 0n, 1n, ps.first_young(c, s0, g), ps.first_n(c, s0, g), fast)
  +n = Su.St.n(Su.go(c, gs, s1))
  +lt = ps.lt_of_le_succ(Su.Cfg.k(c), n, ps.le_k(List.length(&2, Nat, gs), Su.Cfg.k(c), n, many, blk))
  %Equal.sym(Su.St, Su.go(c, List.append(&2, Nat, pre, g <> gs), Su.St.empty()), Su.go(c, g <> gs, s0), ps.go_append(c, pre, g <> gs, Su.St.empty())) : {Su.gives_up(Su.verdict(c, Su.St.n(_))) == True{} : Bool}
  ps.gives_up_of(c, n, lt)

# (D1) timeouts_ordered
# ---------------------

def ps.seen_lost(t: Su.Tm) -> {Nat.is_le(Su.Tm.seen(t), Su.Tm.lost(t)) == True{} : Bool}:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, +relaunch, +startup, +check, +slack, k, bmax, loop, qanswer}:
      ps.le_add(Nat.add(Nat.add(relaunch, startup), check), slack)

def ps.refresh_age(t: Su.Tm) -> {Nat.is_le(Su.Tm.refresh(t), Su.Tm.max_age(t)) == True{} : Bool}:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, +refresh, +boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      ps.le_add(refresh, boot)

def ps.timeouts_ordered(+t: Su.Tm) -> {Su.Tm.ordered(t) == True{} : Bool}:
  +window = Nat.is_le(Nat.mul(Su.Tm.k(t), Su.Tm.loop_step(t)), Su.Tm.window(t))
  +hold = Bool.and(Nat.is_le(Su.Tm.qanswer(t), Su.Tm.quiesce_hold(t)), window)
  +age = Bool.and(Nat.is_le(Su.Tm.refresh(t), Su.Tm.max_age(t)), hold)
  +lost = Bool.and(Nat.is_le(Su.Tm.seen(t), Su.Tm.lost(t)), age)
  +child = Bool.and(Nat.is_le(Nat.add(Su.Tm.stop_grace(t), Su.Tm.drain(t)), Su.Tm.child_kill(t)), lost)
  +drain = Bool.and(Nat.is_le(Su.Tm.drain(t), Su.Tm.launcher_wait(t)), child)
  ps.and_t(Nat.is_le(Su.Tm.teardown(t), Su.Tm.stop_grace(t)), drain, ps.le_add(Su.Tm.teardown(t), Su.Tm.harness(t)),
    ps.and_t(Nat.is_le(Su.Tm.drain(t), Su.Tm.launcher_wait(t)), child, ps.le_add(Su.Tm.drain(t), Su.Tm.margin(t)),
      ps.and_t(Nat.is_le(Nat.add(Su.Tm.stop_grace(t), Su.Tm.drain(t)), Su.Tm.child_kill(t)), lost, ps.le_add(Nat.add(Su.Tm.stop_grace(t), Su.Tm.drain(t)), Su.Tm.margin(t)),
        ps.and_t(Nat.is_le(Su.Tm.seen(t), Su.Tm.lost(t)), age, ps.seen_lost(t),
          ps.and_t(Nat.is_le(Su.Tm.refresh(t), Su.Tm.max_age(t)), hold, ps.refresh_age(t),
            ps.and_t(Nat.is_le(Su.Tm.qanswer(t), Su.Tm.quiesce_hold(t)), window, ps.le_add(Su.Tm.qanswer(t), Su.Tm.stop_grace(t)),
              ps.le_add_l(Su.Tm.loop_step(t), Nat.mul(Su.Tm.k(t), Su.Tm.loop_step(t)))))))))

# (D1) revive_after_refresh
# -------------------------

def ps.tick_at(b: Bool, +h: Nat, +r: Nat, e: {Nat.is_eq(1n+r, h) == b : Bool}, pos: {Nat.is_lt(0n, h) == True{} : Bool}, lt: {Nat.is_lt(r, h) == True{} : Bool}) -> {Nat.is_lt(Rv.tick.put(b, r), h) == True{} : Bool}:
  match b:
    case True{}:
      pos
    case False{}:
      ps.lt_succ_ne(r, h, lt, e)

# a tick keeps the time since the last record below h
def ps.tick_lt(+h: Nat, +r: Nat, pos: {Nat.is_lt(0n, h) == True{} : Bool}, lt: {Nat.is_lt(r, h) == True{} : Bool}) -> {Nat.is_lt(Rv.tick(h, r), h) == True{} : Bool}:
  ps.tick_at(Nat.is_eq(1n+r, h), h, r, {==}, pos, lt)

# so does a run of any length
def ps.since_lt(c: Nat, +h: Nat, +r: Nat, +pos: {Nat.is_lt(0n, h) == True{} : Bool}, lt: {Nat.is_lt(r, h) == True{} : Bool}) -> {Nat.is_lt(Rv.since(c, h, r), h) == True{} : Bool}:
  match c:
    case 0n:
      lt
    case 1n+p:
      ps.since_lt(p, h, Rv.tick(h, r), pos, ps.tick_lt(h, r, pos, lt))

def ps.revive_after_refresh(+h: Nat, +pos: {Nat.is_lt(0n, h) == True{} : Bool}, +b: Nat, +c: Nat, +d: Nat, soon: {Nat.is_le(d, b) == True{} : Bool}) -> {Rv.fresh(Nat.add(h, b), Rv.age(h, c, d)) == True{} : Bool}:
  +a = Rv.since(c, h, 0n)
  +al = ps.lt_le(a, h, ps.since_lt(c, h, 0n, pos, pos))
  ps.le_trans(Nat.add(a, d), Nat.add(a, b), Nat.add(h, b), ps.le_mono(a, d, b, soon), ps.le_mono_r(a, h, b, al))

# (D1) orphan_never_aborts_resumable
# ----------------------------------

def ps.exit_sound(work: Or.Work) -> Or.Sound(Or.Exited{Or.exit.done(Or.orphan_exit(work), work)}):
  match work:
    case Or.Idle{}:
      ({==}, {==})
    case Or.Ongoing{}:
      ({==}, {==})

def ps.check_put(due: Bool, +w: Or.W) -> Or.Sound(Or.check.put(due, w)):
  match due:
    case True{}:
      ps.exit_sound(Or.W.work(w))
    case False{}:
      Unit{}

def ps.check_sound(+window: Nat, +w: Or.W) -> Or.Sound(Or.check(window, w)):
  match w:
    case Or.W{r, q, c, a}:
      ps.check_put(Or.exit_due(window, a, Or.W.work(Or.W{r, q, c, a})), Or.W{r, q, c, a})

def ps.step_sound(+window: Nat, s: Or.St, +e: Or.Ev, ok: Or.Sound(s)) -> Or.Sound(Or.step(window, s, e)):
  match s:
    case Or.Live{w}:
      ps.check_sound(window, Or.apply(w, e))
    case Or.Exited{d}:
      ok

def ps.go_sound(+window: Nat, evs: List<&2, Or.Ev>, +s: Or.St, ok: Or.Sound(s)) -> Or.Sound(Or.go(window, evs, s)):
  match evs:
    case Nil{}:
      ok
    case +e <> rest:
      ps.go_sound(window, rest, Or.step(window, s, e), ps.step_sound(window, s, e, ok))

def ps.orphan_never_aborts_resumable(+window: Nat, +evs: List<&2, Or.Ev>) -> Or.Sound(Or.run(window, evs)):
  ps.go_sound(window, evs, Or.Live{Or.W.empty()}, Unit{})

# (D1) idle_shutdown_never_aborts
# -------------------------------

# a closed gate holds no run
def ps.WOk(w: La.Wk) -> Type:
  match w:
    case La.Wk{b, c}:
      match c:
        case True{}:
          {b == False{} : Bool}
        case False{}:
          Unit

def ps.Inv(ws: List<&2, La.Wk>) -> Type:
  match ws:
    case Nil{}:
      Unit
    case +w <> t:
      (ps.WOk(w) & ps.Inv(t))

# no run aborted, and while the daemon serves, no closed gate holds a run
def ps.Good(s: La.St) -> Type:
  match s:
    case La.St{ws, a, d}:
      match d:
        case True{}:
          {a == 0n : Nat}
        case False{}:
          ({a == 0n : Nat} & ps.Inv(ws))

def ps.prompt_ok(w: La.Wk, ok: ps.WOk(w)) -> ps.WOk(La.prompt(w)):
  match w:
    case La.Wk{b, c}:
      match c:
        case True{}:
          ok
        case False{}:
          Unit{}

def ps.finish_ok(w: La.Wk) -> ps.WOk(La.finish(w)):
  match w:
    case La.Wk{b, c}:
      match c:
        case True{}:
          {==}
        case False{}:
          Unit{}

def ps.quiesce_ok(w: La.Wk, ok: ps.WOk(w)) -> ps.WOk(La.quiesce(w)):
  match w:
    case La.Wk{b, c}:
      match b:
        case True{}:
          ok
        case False{}:
          {==}

def ps.release_ok(w: La.Wk) -> ps.WOk(La.release(w)):
  match w:
    case La.Wk{b, c}:
      Unit{}

def ps.at_prompt(i: Nat, ws: List<&2, La.Wk>, inv: ps.Inv(ws)) -> ps.Inv(La.at(~La.prompt, i, ws)):
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (ps.prompt_ok(w, wo), it)
    case 1n+j:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (wo, ps.at_prompt(j, t, it))

def ps.at_finish(i: Nat, ws: List<&2, La.Wk>, inv: ps.Inv(ws)) -> ps.Inv(La.at(~La.finish, i, ws)):
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (ps.finish_ok(w), it)
    case 1n+j:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (wo, ps.at_finish(j, t, it))

def ps.at_quiesce(i: Nat, ws: List<&2, La.Wk>, inv: ps.Inv(ws)) -> ps.Inv(La.at(~La.quiesce, i, ws)):
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (ps.quiesce_ok(w, wo), it)
    case 1n+j:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (wo, ps.at_quiesce(j, t, it))

def ps.at_release(i: Nat, ws: List<&2, La.Wk>, inv: ps.Inv(ws)) -> ps.Inv(La.at(~La.release, i, ws)):
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (ps.release_ok(w), it)
    case 1n+j:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (wo, ps.at_release(j, t, it))

# every gate closed: no run
def ps.closed_idle(ws: List<&2, La.Wk>, inv: ps.Inv(ws), ac: {La.all_closed(ws) == True{} : Bool}) -> {La.busy_count(ws) == 0n : Nat}:
  match ws:
    case Nil{}:
      {==}
    case w <> t:
      match w:
        case La.Wk{b, c}:
          match b c:
            case True{} False{}:
              ps.absurdF({La.busy_count(La.Wk{True{}, False{}} <> t) == 0n : Nat}, ac)
            case False{} False{}:
              ps.absurdF({La.busy_count(La.Wk{False{}, False{}} <> t) == 0n : Nat}, ac)
            case True{} True{}:
              (wo, it) = inv
              ps.absurd({La.busy_count(La.Wk{True{}, True{}} <> t) == 0n : Nat}, wo)
            case False{} True{}:
              (wo, it) = inv
              ps.closed_idle(t, it, ac)

def ps.commit_good(ok: Bool, +ws: List<&2, La.Wk>, +a: Nat, e: {La.all_closed(ws) == ok : Bool}, ea: {a == 0n : Nat}, inv: ps.Inv(ws)) -> ps.Good(La.commit.put(ok, ws, a)):
  match ok:
    case True{}:
      %Equal.sym(Nat, La.busy_count(ws), 0n, ps.closed_idle(ws, inv, e)) : {Nat.add(_, a) == 0n : Nat}
      ea
    case False{}:
      (ea, inv)

def ps.step_good(s: La.St, +op: La.Op, g: ps.Good(s)) -> ps.Good(La.step(s, op)):
  match s:
    case La.St{+ws, +a, d}:
      match d:
        case True{}:
          g
        case False{}:
          match op:
            case La.Prompt{i}:
              (ea, inv) = g
              (ea, ps.at_prompt(i, ws, inv))
            case La.Finish{i}:
              (ea, inv) = g
              (ea, ps.at_finish(i, ws, inv))
            case La.Quiesce{i}:
              (ea, inv) = g
              (ea, ps.at_quiesce(i, ws, inv))
            case La.Release{i}:
              (ea, inv) = g
              (ea, ps.at_release(i, ws, inv))
            case La.Commit{}:
              (ea, inv) = g
              ps.commit_good(La.all_closed(ws), ws, a, {==}, ea, inv)

def ps.go_good(ops: List<&2, La.Op>, +s: La.St, g: ps.Good(s)) -> ps.Good(La.go(ops, s)):
  match ops:
    case Nil{}:
      g
    case +op <> rest:
      ps.go_good(rest, La.step(s, op), ps.step_good(s, op, g))

def ps.open_inv(bs: List<&2, Bool>) -> ps.Inv(La.open(bs)):
  match bs:
    case Nil{}:
      Unit{}
    case b <> t:
      (Unit{}, ps.open_inv(t))

def ps.aborted_zero(s: La.St, g: ps.Good(s)) -> {La.St.aborted(s) == 0n : Nat}:
  match s:
    case La.St{ws, a, d}:
      match d:
        case True{}:
          g
        case False{}:
          (ea, inv) = g
          ea

def ps.idle_shutdown_never_aborts(+bs: List<&2, Bool>, +ops: List<&2, La.Op>) -> {La.St.aborted(La.run(bs, ops)) == 0n : Nat}:
  ps.aborted_zero(La.run(bs, ops), ps.go_good(ops, La.St{La.open(bs), 0n, False{}}, ({==}, ps.open_inv(bs))))

# (D1) adopt_same_build
# ---------------------

def ps.AD(x: La.Adoption, A: Type) -> Type:
  match x:
    case La.Adopt{}:
      A
    case La.Replace{}:
      Unit

def ps.not_adopted(-A: Type, e: {La.Replace{} == La.Adopt{} : La.Adoption}) -> A:
  %e : ps.AD(_, A)
  Unit{}

def ps.adopt_put(same: Bool, +b: Nat, +sup: Nat, e: {Nat.is_eq(b, sup) == same : Bool}, adopted: {La.adopt.put(same) == La.Adopt{} : La.Adoption}) -> {Some{b} == Some{sup} : Maybe<&2, Nat>}:
  match same:
    case True{}:
      Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, b, sup, ps.eq_of_is_eq(b, sup, e))
    case False{}:
      ps.not_adopted({Some{b} == Some{sup} : Maybe<&2, Nat>}, adopted)

def ps.adopt_same_build(+sup: Nat, w: Maybe<&2, Nat>, adopted: {La.adoption(sup, w) == La.Adopt{} : La.Adoption}) -> {w == Some{sup} : Maybe<&2, Nat>}:
  match w:
    case None{}:
      ps.not_adopted({None{} == Some{sup} : Maybe<&2, Nat>}, adopted)
    case Some{+b}:
      ps.adopt_put(Nat.is_eq(b, sup), b, sup, {==}, adopted)
