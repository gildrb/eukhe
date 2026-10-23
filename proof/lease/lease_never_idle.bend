# eukhe: the proof of LAW lease_never_idle

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease

# Busy: the lease is never free while a live waiter waits
# -------------------------------------------------------

def pl.pick_busy(+n: Nat, q: List<&2, Ls.Waiter>) -> Ls.Busy(Ls.L{n, Ls.pick(q), Ls.after(q)}):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case Ls.Waiter{wk, wo, wl}:
          match wl:
            case True{}:
              Unit{}
            case False{}:
              pl.pick_busy(n, t)

def pl.settle_busy(+n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>) -> Ls.Busy(Ls.settle(n, h, q)):
  match h:
    case None{}:
      pl.pick_busy(n, q)
    case Some{x}:
      Unit{}

def pl.mark_dead(+e: Ls.Ev, q: List<&2, Ls.Waiter>, d: Ls.Dead(q)) -> Ls.Dead(Ls.mark(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, +wo, +wl}:
          (dh, dt) = d
          %Equal.sym(Bool, wl, False{}, dh) : ({Bool.and(_, Bool.not(Ls.hits(e, Ls.Waiter{wk, wo, wl}))) == False{} : Bool} & Ls.Dead(Ls.mark(e, t)))
          ({==}, pl.mark_dead(e, t, dt))

def pl.release_busy(hit: Bool, +x: Ls.Lease, +j: Nat, +n: Nat, +q: List<&2, Ls.Waiter>) -> Ls.Busy(Ls.release.holder(hit, x, j, n, q)):
  match hit:
    case True{}:
      pl.settle_busy(n, None{}, q)
    case False{}:
      Unit{}

def pl.busy_release(+j: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>) -> Ls.Busy(Ls.release(j, n, h, q)):
  match h:
    case None{}:
      pl.settle_busy(n, None{}, Ls.drop(Ls.Release{j}, q))
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          pl.release_busy(Nat.is_eq(hk, j), Ls.Lease{hk, ho}, j, n, q)

def pl.busy_stop(+j: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, b: Ls.Busy(Ls.L{n, h, q})) -> Ls.Busy(Ls.L{n, h, Ls.mark(Ls.Stop{j}, q)}):
  match h:
    case None{}:
      pl.mark_dead(Ls.Stop{j}, q, b)
    case Some{x}:
      Unit{}

def pl.busy_step(+s: Ls.L, +e: Ls.Ev, b: Ls.Busy(s)) -> Ls.Busy(Ls.step(s, e)):
  match s:
    case Ls.L{+n, h, +q}:
      match e:
        case Ls.Ask{p}:
          pl.settle_busy(1n+n, h, List.append(&2, Ls.Waiter, q, [Ls.Waiter{n, p, True{}}]))
        case Ls.Release{+j}:
          pl.busy_release(j, n, h, q)
        case Ls.Stop{+j}:
          pl.busy_stop(j, n, h, q, b)
        case Ls.Crash{+p}:
          pl.settle_busy(n, Ls.crash.holder(p, h), Ls.drop(Ls.Crash{p}, q))

def pl.busy_go(evs: List<&2, Ls.Ev>, +s: Ls.L, b: Ls.Busy(s)) -> Ls.Busy(Ls.go(evs, s)):
  match evs:
    case Nil{}:
      b
    case +e <> rest:
      pl.busy_go(rest, Ls.step(s, e), pl.busy_step(s, e, b))

def lease_never_idle(+evs: List<&2, Ls.Ev>) -> Ls.Busy(Ls.run(evs)):
  pl.busy_go(evs, Ls.L.empty(), Unit{})

def Lease.lease_never_idle(evs):
  lease_never_idle(evs)
