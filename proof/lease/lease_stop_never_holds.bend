# eukhe: the proof of LAW lease_stop_never_holds

import Base
import ../../bend/lease.bend as Ls
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pl.void(-A: Type, e: Empty) -> A:
  match e:

def pl.and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def lease.pl.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      lease.pl.eq_refl(p)

def pl.lt_irrefl(k: Nat) -> {Nat.is_lt(k, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pl.lt_irrefl(p)

def pl.lt_irrefl_at(+a: Nat, +b: Nat, eq: {a == b : Nat}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  %Equal.sym(Nat, a, b, eq) : {Nat.is_lt(_, b) == False{} : Bool}
  pl.lt_irrefl(b)

# a key below another is not it
def pl.ne_of_lt(+a: Nat, +b: Nat, lt: {Nat.is_lt(a, b) == True{} : Bool}, eq: {a == b : Nat}) -> Empty:
  LA.lease.pl.absurd(Empty, Equal.trans(Bool, True{}, Nat.is_lt(a, b), False{}, Equal.sym(Bool, Nat.is_lt(a, b), True{}, lt), pl.lt_irrefl_at(a, b, eq)))

def pl.bounds_up(+l: Nat, +kw: Nat, +kx: Nat, +n: Nat, g: {Nat.is_lt(l, kw) == True{} : Bool}, p: ({Nat.is_lt(kw, kx) == True{} : Bool} & {Nat.is_lt(kx, n) == True{} : Bool})) -> ({Nat.is_lt(l, kx) == True{} : Bool} & {Nat.is_lt(kx, n) == True{} : Bool}):
  (ab, ltn) = p
  (LA.pl.lt_trans(l, kw, kx, g, ab), ltn)

# a waiter is above the bound of its queue, and below the next key
def pl.in_bounds(q: List<&2, Ls.Waiter>, +lo: Maybe<&2, Nat>, +n: Nat, +x: Ls.Waiter, i: Ls.In(x, q), a: Ls.Asc(lo, q), u: LA.pl.Under(n, q)) -> ({Ls.above(Ls.Waiter.key(x), lo) == True{} : Bool} & {Nat.is_lt(Ls.Waiter.key(x), n) == True{} : Bool}):
  match q:
    case Nil{}:
      match i:
    case +w <> +t:
      match lo:
        case None{}:
          match i:
            case Inl{eq}:
              (g, at) = a
              (uw, ut) = u
              %Equal.sym(Ls.Waiter, x, w, eq) : ({True{} == True{} : Bool} & {Nat.is_lt(Ls.Waiter.key(_), n) == True{} : Bool})
              ({==}, uw)
            case Inr{it}:
              (g, at) = a
              (uw, ut) = u
              ({==}, Pair.snd({Ls.above(Ls.Waiter.key(x), Some{Ls.Waiter.key(w)}) == True{} : Bool}, {Nat.is_lt(Ls.Waiter.key(x), n) == True{} : Bool}, pl.in_bounds(t, Some{Ls.Waiter.key(w)}, n, x, it, at, ut)))
        case Some{+l}:
          match i:
            case Inl{eq}:
              (g, at) = a
              (uw, ut) = u
              %Equal.sym(Ls.Waiter, x, w, eq) : ({Nat.is_lt(l, Ls.Waiter.key(_)) == True{} : Bool} & {Nat.is_lt(Ls.Waiter.key(_), n) == True{} : Bool})
              (g, uw)
            case Inr{it}:
              (g, at) = a
              (uw, ut) = u
              pl.bounds_up(l, Ls.Waiter.key(w), Ls.Waiter.key(x), n, g, pl.in_bounds(t, Some{Ls.Waiter.key(w)}, n, x, it, at, ut))

# A stopped waiter never holds
# ----------------------------

# no live waiter of q has key k
def pl.NoLive(+k: Nat, q: List<&2, Ls.Waiter>) -> Type:
  match q:
    case Nil{}:
      Unit
    case +w <> +t:
      (({Ls.Waiter.key(w) == k : Nat} -> {Ls.Waiter.live(w) == False{} : Bool}) & pl.NoLive(k, t))

# k neither holds nor waits live, and every new key is above it
def pl.Gone(+k: Nat, s: Ls.L) -> Type:
  match s:
    case Ls.L{+n, +h, +q}:
      (Ls.NotHeld(k, h) & (pl.NoLive(k, q) & {Nat.is_lt(k, n) == True{} : Bool}))

def pl.kill(+wk: Nat, +k: Nat, +wl: Bool, eq: {wk == k : Nat}) -> {Bool.and(wl, Bool.not(Nat.is_eq(wk, k))) == False{} : Bool}:
  %Equal.sym(Nat, wk, k, eq) : {Bool.and(wl, Bool.not(Nat.is_eq(_, k))) == False{} : Bool}
  %lease.pl.eq_refl(k) : {Bool.and(wl, Bool.not(_)) == False{} : Bool}
  pl.and_false(wl)

# a stop of k leaves no live waiter of k
def pl.mark_kills(+k: Nat, q: List<&2, Ls.Waiter>) -> pl.NoLive(k, Ls.mark(Ls.Stop{k}, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, +wo, +wl}:
          (eq => pl.kill(wk, k, wl, eq), pl.mark_kills(k, t))

def pl.dead_and(+wl: Bool, +x: Bool, f: {wl == False{} : Bool}) -> {Bool.and(wl, x) == False{} : Bool}:
  %Equal.sym(Bool, wl, False{}, f) : {Bool.and(_, x) == False{} : Bool}
  {==}

def pl.nolive_mark(+e: Ls.Ev, +k: Nat, q: List<&2, Ls.Waiter>, nl: pl.NoLive(k, q)) -> pl.NoLive(k, Ls.mark(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, +wo, +wl}:
          (f, nt) = nl
          (eq => pl.dead_and(wl, Bool.not(Ls.hits(e, Ls.Waiter{wk, wo, wl})), f(eq)), pl.nolive_mark(e, k, t, nt))

def pl.nolive_put(b: Bool, +k: Nat, +w: Ls.Waiter, +r: List<&2, Ls.Waiter>, f: {Ls.Waiter.key(w) == k : Nat} -> {Ls.Waiter.live(w) == False{} : Bool}, nr: pl.NoLive(k, r)) -> pl.NoLive(k, Ls.drop.put(b, w, r)):
  match b:
    case True{}:
      nr
    case False{}:
      (f, nr)

def pl.nolive_drop(+e: Ls.Ev, +k: Nat, q: List<&2, Ls.Waiter>, nl: pl.NoLive(k, q)) -> pl.NoLive(k, Ls.drop(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case +w <> +t:
      (f, nt) = nl
      pl.nolive_put(Ls.hits(e, w), k, w, Ls.drop(e, t), f, pl.nolive_drop(e, k, t, nt))

def pl.fresh(+k: Nat, +n: Nat, lt: {Nat.is_lt(k, n) == True{} : Bool}, eq: {n == k : Nat}) -> {True{} == False{} : Bool}:
  pl.void({True{} == False{} : Bool}, pl.ne_of_lt(k, n, lt, Equal.sym(Nat, n, k, eq)))

def pl.nolive_snoc(+k: Nat, +n: Nat, +o: Nat, q: List<&2, Ls.Waiter>, nl: pl.NoLive(k, q), lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.NoLive(k, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, o, True{}}])):
  match q:
    case Nil{}:
      (eq => pl.fresh(k, n, lt, eq), Unit{})
    case +w <> +t:
      (f, nt) = nl
      (f, pl.nolive_snoc(k, n, o, t, nt, lt))

def pl.pick_gone(+k: Nat, +n: Nat, q: List<&2, Ls.Waiter>, nl: pl.NoLive(k, q), lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.Gone(k, Ls.L{n, Ls.pick(q), Ls.after(q)}):
  match q:
    case Nil{}:
      (Unit{}, (Unit{}, lt))
    case w <> +t:
      match w:
        case Ls.Waiter{wk, wo, wl}:
          match wl:
            case True{}:
              (f, nt) = nl
              (eq => LA.lease.pl.absurd(Empty, f(eq)), (nt, lt))
            case False{}:
              (f, nt) = nl
              pl.pick_gone(k, n, t, nt, lt)

def pl.settle_gone(+k: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, nh: Ls.NotHeld(k, h), nl: pl.NoLive(k, q), lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.Gone(k, Ls.settle(n, h, q)):
  match h:
    case None{}:
      pl.pick_gone(k, n, q, nl, lt)
    case Some{x}:
      (nh, (nl, lt))

def pl.release_gone(hit: Bool, +hk: Nat, +ho: Nat, +j: Nat, +k: Nat, +n: Nat, +q: List<&2, Ls.Waiter>, nh: Ls.NotHeld(k, Some{Ls.Lease{hk, ho}}), nl: pl.NoLive(k, q), lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.Gone(k, Ls.release.holder(hit, Ls.Lease{hk, ho}, j, n, q)):
  match hit:
    case True{}:
      pl.settle_gone(k, n, None{}, q, Unit{}, nl, lt)
    case False{}:
      (nh, (pl.nolive_drop(Ls.Release{j}, k, q, nl), lt))

def pl.crash_gone(hit: Bool, +hk: Nat, +ho: Nat, +k: Nat, nh: Ls.NotHeld(k, Some{Ls.Lease{hk, ho}})) -> Ls.NotHeld(k, Ls.crash.put(hit, Ls.Lease{hk, ho})):
  match hit:
    case True{}:
      Unit{}
    case False{}:
      nh

def pl.crash_notheld(+p: Nat, +k: Nat, h: Maybe<&2, Ls.Lease>, nh: Ls.NotHeld(k, h)) -> Ls.NotHeld(k, Ls.crash.holder(p, h)):
  match h:
    case None{}:
      Unit{}
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          pl.crash_gone(Nat.is_eq(ho, p), hk, ho, k, nh)

def pl.gone_release(+j: Nat, +k: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, g: pl.Gone(k, Ls.L{n, h, q})) -> pl.Gone(k, Ls.release(j, n, h, q)):
  match h:
    case None{}:
      (nh, rest) = g
      (nl, lt) = rest
      pl.settle_gone(k, n, None{}, Ls.drop(Ls.Release{j}, q), Unit{}, pl.nolive_drop(Ls.Release{j}, k, q, nl), lt)
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          (nh, rest) = g
          (nl, lt) = rest
          pl.release_gone(Nat.is_eq(hk, j), hk, ho, j, k, n, q, nh, nl, lt)

def pl.gone_ask(+k: Nat, +n: Nat, +p: Nat, +h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, nh: Ls.NotHeld(k, h), nl: pl.NoLive(k, q), +lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.Gone(k, Ls.settle(1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, p, True{}}]))):
  pl.settle_gone(k, 1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, p, True{}}]), nh, pl.nolive_snoc(k, n, p, q, nl, lt), LA.pl.lt_succ(k, n, lt))

def pl.gone_step(+k: Nat, +s: Ls.L, +e: Ls.Ev, g: pl.Gone(k, s)) -> pl.Gone(k, Ls.step(s, e)):
  match s:
    case Ls.L{+n, +h, +q}:
      match e:
        case Ls.Ask{+p}:
          (nh, rest) = g
          (nl, lt) = rest
          pl.gone_ask(k, n, p, h, q, nh, nl, lt)
        case Ls.Release{+j}:
          pl.gone_release(j, k, n, h, q, g)
        case Ls.Stop{+j}:
          (nh, rest) = g
          (nl, lt) = rest
          (nh, (pl.nolive_mark(Ls.Stop{j}, k, q, nl), lt))
        case Ls.Crash{+p}:
          (nh, rest) = g
          (nl, lt) = rest
          pl.settle_gone(k, n, Ls.crash.holder(p, h), Ls.drop(Ls.Crash{p}, q), pl.crash_notheld(p, k, h, nh), pl.nolive_drop(Ls.Crash{p}, k, q, nl), lt)

def pl.gone_go(+k: Nat, evs: List<&2, Ls.Ev>, +s: Ls.L, g: pl.Gone(k, s)) -> pl.Gone(k, Ls.go(evs, s)):
  match evs:
    case Nil{}:
      g
    case +e <> rest:
      pl.gone_go(k, rest, Ls.step(s, e), pl.gone_step(k, s, e, g))

def pl.gone_holder(h: Maybe<&2, Ls.Lease>, +k: Nat, ab: {Ls.above(k, Ls.hkey(h)) == True{} : Bool}) -> Ls.NotHeld(k, h):
  match h:
    case None{}:
      Unit{}
    case Some{x}:
      match x:
        case Ls.Lease{+hk, ho}:
          eq => pl.ne_of_lt(hk, k, ab, eq)

def pl.gone_of(h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, +k: Nat, +n: Nat, p: ({Ls.above(k, Ls.hkey(h)) == True{} : Bool} & {Nat.is_lt(k, n) == True{} : Bool})) -> pl.Gone(k, Ls.L{n, h, Ls.mark(Ls.Stop{k}, q)}):
  (ab, lt) = p
  (pl.gone_holder(h, k, ab), (pl.mark_kills(k, q), lt))

# a stop of a live waiter makes it gone
def pl.gone_start(+s: Ls.L, +k: Nat, +o: Nat, inv: LA.pl.Inv(s), i: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(s))) -> pl.Gone(k, Ls.step(s, Ls.Stop{k})):
  match s:
    case Ls.L{+n, +h, +q}:
      (a, uh) = inv
      (u, hu) = uh
      pl.gone_of(h, q, k, n, pl.in_bounds(q, Ls.hkey(h), n, Ls.Waiter{k, o, True{}}, i, a, u))

def pl.gone_held(+k: Nat, +s: Ls.L, g: pl.Gone(k, s)) -> Ls.NotHeld(k, Ls.L.holder(s)):
  match s:
    case Ls.L{n, h, q}:
      (nh, _) = g
      nh

def lease_stop_never_holds(+evs: List<&2, Ls.Ev>, +k: Nat, +o: Nat, +rest: List<&2, Ls.Ev>, waits: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(Ls.run(evs)))) -> Ls.NotHeld(k, Ls.L.holder(Ls.go(rest, Ls.step(Ls.run(evs), Ls.Stop{k})))):
  +s = Ls.step(Ls.run(evs), Ls.Stop{k})
  pl.gone_held(k, Ls.go(rest, s), pl.gone_go(k, rest, s, pl.gone_start(Ls.run(evs), k, o, LA.pl.inv_run(evs), waits)))

def Laws.lease_stop_never_holds(evs, k, o, rest, waits):
  lease_stop_never_holds(evs, k, o, rest, waits)
