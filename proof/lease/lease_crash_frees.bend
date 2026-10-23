# eukhe: the proof of LAW lease_crash_frees

import Base
import ../../bend/lease.bend as Ls
import ../../LAWS.bend as Laws

# A crash frees its origin
# ------------------------

def pl.none_put(+p: Nat, +wk: Nat, +wo: Nat, +wl: Bool, b: Bool, eb: {Nat.is_eq(wo, p) == b : Bool}, +r: List<&2, Ls.Waiter>, nr: Ls.NoneFrom(p, r)) -> Ls.NoneFrom(p, Ls.drop.put(b, Ls.Waiter{wk, wo, wl}, r)):
  match b:
    case True{}:
      nr
    case False{}:
      (eb, nr)

def pl.none_drop(+p: Nat, q: List<&2, Ls.Waiter>) -> Ls.NoneFrom(p, Ls.drop(Ls.Crash{p}, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, +wo, +wl}:
          pl.none_put(p, wk, wo, wl, Nat.is_eq(wo, p), {==}, Ls.drop(Ls.Crash{p}, t), pl.none_drop(p, t))

def pl.pick_freed(+p: Nat, +n: Nat, q: List<&2, Ls.Waiter>, nf: Ls.NoneFrom(p, q)) -> Ls.Freed(p, Ls.L{n, Ls.pick(q), Ls.after(q)}):
  match q:
    case Nil{}:
      (Unit{}, Unit{})
    case w <> +t:
      match w:
        case Ls.Waiter{wk, wo, wl}:
          match wl:
            case True{}:
              nf
            case False{}:
              (e, nt) = nf
              pl.pick_freed(p, n, t, nt)

def pl.crash_put(+p: Nat, b: Bool, +hk: Nat, +ho: Nat, eb: {Nat.is_eq(ho, p) == b : Bool}) -> Ls.NotFrom(p, Ls.crash.put(b, Ls.Lease{hk, ho})):
  match b:
    case True{}:
      Unit{}
    case False{}:
      eb

def pl.crash_holder(+p: Nat, h: Maybe<&2, Ls.Lease>) -> Ls.NotFrom(p, Ls.crash.holder(p, h)):
  match h:
    case None{}:
      Unit{}
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          pl.crash_put(p, Nat.is_eq(ho, p), hk, ho, {==})

def pl.settle_freed(+p: Nat, +n: Nat, h: Maybe<&2, Ls.Lease>, +q: List<&2, Ls.Waiter>, nh: Ls.NotFrom(p, h), nq: Ls.NoneFrom(p, q)) -> Ls.Freed(p, Ls.settle(n, h, q)):
  match h:
    case None{}:
      pl.pick_freed(p, n, q, nq)
    case Some{x}:
      (nh, nq)

def lease_crash_frees(+s: Ls.L, +p: Nat) -> Ls.Freed(p, Ls.step(s, Ls.Crash{p})):
  match s:
    case Ls.L{+n, h, +q}:
      pl.settle_freed(p, n, Ls.crash.holder(p, h), Ls.drop(Ls.Crash{p}, q), pl.crash_holder(p, h), pl.none_drop(p, q))

def Laws.lease_crash_frees(s, p):
  lease_crash_frees(s, p)
