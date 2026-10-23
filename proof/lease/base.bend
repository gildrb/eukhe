# eukhe: lemmas the proofs of area lease share

import Base
import ../../bend/lease.bend as Ls

# ---- lease ----

# proof_lease: the lease laws of LAWS.bend (H6). Every event keeps an
# invariant of the reachable states: the holder came before every waiter,
# the waiters wait in arrival order, and every key is below the next one
# (`pl.Inv`). From it: first come, first served (`lease_fifo`); the lease
# is never free while a live waiter waits (`lease_never_idle`); no event
# drops a waiter it does not name (`lease_keeps_waiters`); a waiter that
# stopped waiting never holds the lease (`lease_stop_never_holds`); a
# crash frees every lease of its origin (`lease_crash_frees`).

# Logic and numbers
# -----------------

def lease.pl.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def lease.pl.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : lease.pl.BD(_, Unit, A)
  Unit{}

def lease.pl.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : lease.pl.BD(_, A, Unit)
  Unit{}

def pl.lt_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pl.lt_self(p)

def pl.lt_succ(k: Nat, n: Nat, h: {Nat.is_lt(k, n) == True{} : Bool}) -> {Nat.is_lt(k, 1n+n) == True{} : Bool}:
  match k n:
    case 0n _:
      {==}
    case 1n+p 0n:
      lease.pl.absurdF({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+m:
      pl.lt_succ(p, m, h)

def pl.lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      lease.pl.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      lease.pl.absurdF({Nat.is_lt(a, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      pl.lt_trans(p, q, r, ab, bc)

# The invariant: arrival order, keys below the next
# -------------------------------------------------

def pl.Under(+n: Nat, q: List<&2, Ls.Waiter>) -> Data:
  match q:
    case Nil{}:
      Unit
    case +w <> +t:
      Sigma<&2, &2, {Nat.is_lt(Ls.Waiter.key(w), n) == True{} : Bool}, _ => pl.Under(n, t)>

def pl.HUnder(+n: Nat, h: Maybe<&2, Ls.Lease>) -> Data:
  match h:
    case None{}:
      Unit
    case Some{x}:
      match x:
        case Ls.Lease{hk, ho}:
          {Nat.is_lt(hk, n) == True{} : Bool}

def pl.Inv(s: Ls.L) -> Type:
  match s:
    case Ls.L{+n, +h, +q}:
      (Ls.Asc(Ls.hkey(h), q) & Sigma<&2, &2, pl.Under(n, q), _ => pl.HUnder(n, h)>)

def pl.asc_none(lo: Maybe<&2, Nat>, q: List<&2, Ls.Waiter>, a: Ls.Asc(lo, q)) -> Ls.Asc(None{}, q):
  match q:
    case Nil{}:
      Unit{}
    case +w <> +t:
      (_, at) = a
      ({==}, at)

# a looser bound
def pl.weaken(lo: Maybe<&2, Nat>, +l: Nat, r: List<&2, Ls.Waiter>, g: {Ls.above(l, lo) == True{} : Bool}, ar: Ls.Asc(Some{l}, r)) -> Ls.Asc(lo, r):
  match lo:
    case None{}:
      pl.asc_none(Some{l}, r, ar)
    case Some{+l0}:
      match r:
        case Nil{}:
          Unit{}
        case +w <> +t:
          (g2, at) = ar
          (pl.lt_trans(l0, l, Ls.Waiter.key(w), g, g2), at)

def pl.asc_put(b: Bool, +lo: Maybe<&2, Nat>, +w: Ls.Waiter, +r: List<&2, Ls.Waiter>, g: {Ls.above(Ls.Waiter.key(w), lo) == True{} : Bool}, ar: Ls.Asc(Some{Ls.Waiter.key(w)}, r)) -> Ls.Asc(lo, Ls.drop.put(b, w, r)):
  match b:
    case True{}:
      pl.weaken(lo, Ls.Waiter.key(w), r, g, ar)
    case False{}:
      (g, ar)

def pl.asc_drop(+e: Ls.Ev, q: List<&2, Ls.Waiter>, +lo: Maybe<&2, Nat>, a: Ls.Asc(lo, q)) -> Ls.Asc(lo, Ls.drop(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case +w <> +t:
      (g, at) = a
      pl.asc_put(Ls.hits(e, w), lo, w, Ls.drop(e, t), g, pl.asc_drop(e, t, Some{Ls.Waiter.key(w)}, at))

def pl.asc_mark(+e: Ls.Ev, q: List<&2, Ls.Waiter>, +lo: Maybe<&2, Nat>, a: Ls.Asc(lo, q)) -> Ls.Asc(lo, Ls.mark(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, wo, wl}:
          (g, at) = a
          (g, pl.asc_mark(e, t, Some{wk}, at))

def pl.asc_snoc(q: List<&2, Ls.Waiter>, +lo: Maybe<&2, Nat>, +n: Nat, +o: Nat, a: Ls.Asc(lo, q), u: pl.Under(n, q), g: {Ls.above(n, lo) == True{} : Bool}) -> Ls.Asc(lo, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, o, True{}}])):
  match q:
    case Nil{}:
      (g, Unit{})
    case +w <> +t:
      (gw, at) = a
      (uw, ut) = u
      (gw, pl.asc_snoc(t, Some{Ls.Waiter.key(w)}, n, o, at, ut, uw))

def pl.under_put(b: Bool, +n: Nat, +w: Ls.Waiter, +r: List<&2, Ls.Waiter>, uw: {Nat.is_lt(Ls.Waiter.key(w), n) == True{} : Bool}, ur: pl.Under(n, r)) -> pl.Under(n, Ls.drop.put(b, w, r)):
  match b:
    case True{}:
      ur
    case False{}:
      (uw, ur)

def pl.under_drop(+e: Ls.Ev, q: List<&2, Ls.Waiter>, +n: Nat, u: pl.Under(n, q)) -> pl.Under(n, Ls.drop(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case +w <> +t:
      (uw, ut) = u
      pl.under_put(Ls.hits(e, w), n, w, Ls.drop(e, t), uw, pl.under_drop(e, t, n, ut))

def pl.under_mark(+e: Ls.Ev, q: List<&2, Ls.Waiter>, +n: Nat, u: pl.Under(n, q)) -> pl.Under(n, Ls.mark(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case Ls.Waiter{wk, wo, wl}:
          (uw, ut) = u
          (uw, pl.under_mark(e, t, n, ut))

def pl.under_snoc(q: List<&2, Ls.Waiter>, +n: Nat, +o: Nat, u: pl.Under(n, q)) -> pl.Under(1n+n, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, o, True{}}])):
  match q:
    case Nil{}:
      (pl.lt_self(n), Unit{})
    case +w <> +t:
      (uw, ut) = u
      (pl.lt_succ(Ls.Waiter.key(w), n, uw), pl.under_snoc(t, n, o, ut))

def pl.hunder_succ(+n: Nat, h: Maybe<&2, Ls.Lease>, hu: pl.HUnder(n, h)) -> pl.HUnder(1n+n, h):
  match h:
    case None{}:
      Unit{}
    case Some{x}:
      match x:
        case Ls.Lease{hk, ho}:
          pl.lt_succ(hk, n, hu)

def pl.h_above(+n: Nat, h: Maybe<&2, Ls.Lease>, hu: pl.HUnder(n, h)) -> {Ls.above(n, Ls.hkey(h)) == True{} : Bool}:
  match h:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Ls.Lease{hk, ho}:
          hu

def pl.pick_inv(+n: Nat, q: List<&2, Ls.Waiter>, +lo: Maybe<&2, Nat>, a: Ls.Asc(lo, q), u: pl.Under(n, q)) -> pl.Inv(Ls.L{n, Ls.pick(q), Ls.after(q)}):
  match q:
    case Nil{}:
      (Unit{}, (Unit{}, Unit{}))
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, wo, wl}:
          match wl:
            case True{}:
              (g, at) = a
              (uw, ut) = u
              (at, (ut, uw))
            case False{}:
              (g, at) = a
              (uw, ut) = u
              pl.pick_inv(n, t, Some{wk}, at, ut)

def pl.settle_inv(+n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, a: Ls.Asc(Ls.hkey(h), q), u: pl.Under(n, q), hu: pl.HUnder(n, h)) -> pl.Inv(Ls.settle(n, h, q)):
  match h:
    case None{}:
      pl.pick_inv(n, q, None{}, a, u)
    case Some{x}:
      (a, (u, hu))

def pl.release_inv(hit: Bool, +hk: Nat, +ho: Nat, +j: Nat, +n: Nat, +q: List<&2, Ls.Waiter>, a: Ls.Asc(Some{hk}, q), u: pl.Under(n, q), hu: {Nat.is_lt(hk, n) == True{} : Bool}) -> pl.Inv(Ls.release.holder(hit, Ls.Lease{hk, ho}, j, n, q)):
  match hit:
    case True{}:
      pl.settle_inv(n, None{}, q, pl.asc_none(Some{hk}, q, a), u, Unit{})
    case False{}:
      (pl.asc_drop(Ls.Release{j}, q, Some{hk}, a), (pl.under_drop(Ls.Release{j}, q, n, u), hu))

def pl.crash_inv(hit: Bool, +hk: Nat, +ho: Nat, +p: Nat, +n: Nat, +q: List<&2, Ls.Waiter>, a: Ls.Asc(Some{hk}, q), u: pl.Under(n, q), hu: {Nat.is_lt(hk, n) == True{} : Bool}) -> pl.Inv(Ls.settle(n, Ls.crash.put(hit, Ls.Lease{hk, ho}), Ls.drop(Ls.Crash{p}, q))):
  match hit:
    case True{}:
      pl.settle_inv(n, None{}, Ls.drop(Ls.Crash{p}, q), pl.asc_none(Some{hk}, Ls.drop(Ls.Crash{p}, q), pl.asc_drop(Ls.Crash{p}, q, Some{hk}, a)), pl.under_drop(Ls.Crash{p}, q, n, u), Unit{})
    case False{}:
      (pl.asc_drop(Ls.Crash{p}, q, Some{hk}, a), (pl.under_drop(Ls.Crash{p}, q, n, u), hu))

def pl.inv_ask.go(+p: Nat, +n: Nat, +h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, a: Ls.Asc(Ls.hkey(h), q), uh: Sigma<&2, &2, pl.Under(n, q), _ => pl.HUnder(n, h)>) -> pl.Inv(Ls.settle(1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, p, True{}}]))):
  (+u, +hu) = uh
  pl.settle_inv(1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, p, True{}}]), pl.asc_snoc(q, Ls.hkey(h), n, p, a, u, pl.h_above(n, h, hu)), pl.under_snoc(q, n, p, u), pl.hunder_succ(n, h, hu))

def pl.inv_ask(+p: Nat, +n: Nat, +h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, inv: pl.Inv(Ls.L{n, h, q})) -> pl.Inv(Ls.settle(1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, p, True{}}]))):
  (a, uh) = inv
  pl.inv_ask.go(p, n, h, q, a, uh)

def pl.inv_release(+j: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, inv: pl.Inv(Ls.L{n, h, q})) -> pl.Inv(Ls.release(j, n, h, q)):
  match h:
    case None{}:
      (a, uh) = inv
      (u, hu) = uh
      pl.settle_inv(n, None{}, Ls.drop(Ls.Release{j}, q), pl.asc_drop(Ls.Release{j}, q, None{}, a), pl.under_drop(Ls.Release{j}, q, n, u), Unit{})
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          (a, uh) = inv
          (u, hu) = uh
          pl.release_inv(Nat.is_eq(hk, j), hk, ho, j, n, q, a, u, hu)

def pl.inv_stop(+j: Nat, +n: Nat, +h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, inv: pl.Inv(Ls.L{n, h, q})) -> pl.Inv(Ls.L{n, h, Ls.mark(Ls.Stop{j}, q)}):
  (a, uh) = inv
  (u, hu) = uh
  (pl.asc_mark(Ls.Stop{j}, q, Ls.hkey(h), a), (pl.under_mark(Ls.Stop{j}, q, n, u), hu))

def pl.inv_crash(+p: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, inv: pl.Inv(Ls.L{n, h, q})) -> pl.Inv(Ls.settle(n, Ls.crash.holder(p, h), Ls.drop(Ls.Crash{p}, q))):
  match h:
    case None{}:
      (a, uh) = inv
      (u, hu) = uh
      pl.settle_inv(n, None{}, Ls.drop(Ls.Crash{p}, q), pl.asc_drop(Ls.Crash{p}, q, None{}, a), pl.under_drop(Ls.Crash{p}, q, n, u), Unit{})
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          (a, uh) = inv
          (u, hu) = uh
          pl.crash_inv(Nat.is_eq(ho, p), hk, ho, p, n, q, a, u, hu)

def pl.inv_step(+s: Ls.L, +e: Ls.Ev, inv: pl.Inv(s)) -> pl.Inv(Ls.step(s, e)):
  match s:
    case Ls.L{+n, +h, +q}:
      match e:
        case Ls.Ask{+p}:
          pl.inv_ask(p, n, h, q, inv)
        case Ls.Release{+j}:
          pl.inv_release(j, n, h, q, inv)
        case Ls.Stop{+j}:
          pl.inv_stop(j, n, h, q, inv)
        case Ls.Crash{+p}:
          pl.inv_crash(p, n, h, q, inv)

def pl.inv_go(evs: List<&2, Ls.Ev>, +s: Ls.L, inv: pl.Inv(s)) -> pl.Inv(Ls.go(evs, s)):
  match evs:
    case Nil{}:
      inv
    case +e <> rest:
      pl.inv_go(rest, Ls.step(s, e), pl.inv_step(s, e, inv))

def pl.inv_run(+evs: List<&2, Ls.Ev>) -> pl.Inv(Ls.run(evs)):
  pl.inv_go(evs, Ls.L.empty(), (Unit{}, (Unit{}, Unit{})))
