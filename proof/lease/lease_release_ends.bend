# eukhe: the proof of LAW lease_release_ends
# A release of j drops every waiter of key j; when j holds, the holder
# came before every waiter (LA.pl.inv_run), so no waiter has key j and
# the grant that follows picks a waiter that is not j.

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease
import ./base.bend as LA
import ./lease_undelivered_is_stopped.bend as LU

def re.sym_refl(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {True{} == Nat.is_eq(a, b) : Bool}:
  %Equal.sym(Nat, a, b, e) : {True{} == Nat.is_eq(_, b) : Bool}
  LU.lu.eq_refl(b)

# a == b and is_eq(a, b) == False: impossible
def re.ne(+a: Nat, +b: Nat, f: {Nat.is_eq(a, b) == False{} : Bool}, e: {a == b : Nat}) -> Empty:
  LA.lease.pl.absurd(Empty, Equal.trans(Bool, True{}, Nat.is_eq(a, b), False{}, re.sym_refl(a, b, e), f))

def re.eq_of(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      LA.lease.pl.absurdF({0n == 1n+y : Nat}, h)
    case 1n+x 0n:
      LA.lease.pl.absurdF({1n+x == 0n : Nat}, h)
    case 1n+x 1n+y:
      Equal.cong(Nat, Nat, v => 1n+v, x, y, re.eq_of(x, y, h))

def re.put(b: Bool, +wk: Nat, +wo: Nat, +wl: Bool, +j: Nat, r: List<&2, Ls.Waiter>, eb: {Nat.is_eq(wk, j) == b : Bool}, nr: Lease.lw_NoKey(j, r)) -> Lease.lw_NoKey(j, Ls.drop.put(b, Ls.Waiter{wk, wo, wl}, r)):
  match b:
    case True{}:
      nr
    case False{}:
      (eb, nr)

# a release of j drops every waiter of key j
def re.nokey_drop(+j: Nat, q: List<&2, Ls.Waiter>) -> Lease.lw_NoKey(j, Ls.drop(Ls.Release{j}, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, +wo, +wl}:
          re.put(Nat.is_eq(wk, j), wk, wo, wl, j, Ls.drop(Ls.Release{j}, t), {==}, re.nokey_drop(j, t))

# no waiter after a key below them all is that key
def re.above(+j: Nat, q: List<&2, Ls.Waiter>, a: Ls.Asc(Some{j}, q)) -> Lease.lw_NoKey(j, q):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, wo, wl}:
          (+g, at) = a
          (LU.lu.lt_ne(j, wk, g), re.above(j, t, LA.pl.weaken(Some{j}, wk, t, g, at)))

# the grant from a queue with no waiter j gives the lease to no j
def re.pick(+j: Nat, +n: Nat, q: List<&2, Ls.Waiter>, nk: Lease.lw_NoKey(j, q)) -> Lease.lw_Over(j, Ls.L{n, Ls.pick(q), Ls.after(q)}):
  match q:
    case Nil{}:
      (Unit{}, Unit{})
    case w <> t:
      match w:
        case Ls.Waiter{+wk, wo, wl}:
          match wl:
            case True{}:
              (+ew, nt) = nk
              (e => re.ne(wk, j, ew, e), nt)
            case False{}:
              (ew, nt) = nk
              re.pick(j, n, t, nt)

def re.hit(b: Bool, +hk: Nat, +ho: Nat, +j: Nat, +n: Nat, +q: List<&2, Ls.Waiter>, a: Ls.Asc(Some{hk}, q), eb: {Nat.is_eq(hk, j) == b : Bool}) -> Lease.lw_Over(j, Ls.release.holder(b, Ls.Lease{hk, ho}, j, n, q)):
  match b:
    case True{}:
      re.pick(j, n, q, re.above(j, q, LU.lu.asc_at(hk, j, re.eq_of(hk, j, eb), q, a)))
    case False{}:
      (e => re.ne(hk, j, eb, e), re.nokey_drop(j, q))

def re.go(+s: Ls.L, +j: Nat, inv: LA.pl.Inv(s)) -> Lease.lw_Over(j, Ls.step(s, Ls.Release{j})):
  match s:
    case Ls.L{+n, h, +q}:
      match h:
        case None{}:
          re.pick(j, n, Ls.drop(Ls.Release{j}, q), re.nokey_drop(j, q))
        case Some{x}:
          match x:
            case Ls.Lease{+hk, +ho}:
              (a, uh) = inv
              re.hit(Nat.is_eq(hk, j), hk, ho, j, n, q, a, {==})

def Lease.lease_release_ends(evs, j):
  re.go(Ls.run(evs), j, LA.pl.inv_run(evs))
