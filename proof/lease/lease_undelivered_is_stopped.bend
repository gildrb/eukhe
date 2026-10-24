# eukhe: the proof of LAW lease_undelivered_is_stopped
# In a reachable state the holder came before every waiter and the lease
# is never free while a live waiter waits (LA.pl.inv_run, LNI). So an
# event hands the lease to a waiting k only when it ends the holder (a
# release or a crash of its origin), and k is then the first live waiter
# of the queue left: releasing k at once leaves the waiters after k, and
# stopping k first makes the same grant pass k over (`lu.pm`): no other
# waiter has key k (the keys rise, `lu.mk`), and a crash drops the same
# waiters whether k stopped or not (`lu.drop_mark`).

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease
import ./base.bend as LA
import ./lease_never_idle.bend as LNI
import ./lease_stop_never_holds.bend as LSN

# Logic
# -----

def lu.MD(m: Maybe<&2, Ls.Lease>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def lu.none_some(-G: Type, -x: Ls.Lease, h: {None{} == Some{x} : Maybe<&2, Ls.Lease>}) -> G:
  %h : lu.MD(_, G)
  Unit{}

def lu.hk(m: Maybe<&2, Ls.Lease>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      match x:
        case Ls.Lease{k, o}:
          k

def lu.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      lu.eq_refl(p)

def lu.lt_ne(k: Nat, w: Nat, lt: {Nat.is_lt(k, w) == True{} : Bool}) -> {Nat.is_eq(w, k) == False{} : Bool}:
  match k w:
    case 0n 0n:
      LA.lease.pl.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, lt)
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      LA.lease.pl.absurdF({Nat.is_eq(0n, 1n+a) == False{} : Bool}, lt)
    case 1n+a 1n+b:
      lu.lt_ne(a, b, lt)

def lu.and_true(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# once wk is k, a stop of k kills wk
def lu.not_self(+wk: Nat, +k: Nat, eq: {wk == k : Nat}) -> {False{} == Bool.not(Nat.is_eq(wk, k)) : Bool}:
  %eq : {False{} == Bool.not(Nat.is_eq(wk, _)) : Bool}
  %lu.eq_refl(wk) : {False{} == Bool.not(_) : Bool}
  {==}

# a bound that is equal
def lu.asc_at(+wk: Nat, +k: Nat, eq: {wk == k : Nat}, t: List<&2, Ls.Waiter>, a: Ls.Asc(Some{wk}, t)) -> Ls.Asc(Some{k}, t):
  %eq : Ls.Asc(Some{_}, t)
  a

# a holder with the key of a waiter: impossible, the holder came first
def lu.not_held(-G: Type, +hk: Nat, +ho: Nat, +k: Nat, +o: Nat, +n: Nat, q: List<&2, Ls.Waiter>, a: Ls.Asc(Some{hk}, q), u: LA.pl.Under(n, q), waits: Ls.In(Ls.Waiter{k, o, True{}}, q), got: {Some{Ls.Lease{hk, ho}} == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}) -> G:
  +eq = Equal.cong(Maybe<&2, Ls.Lease>, Nat, m => lu.hk(m), Some{Ls.Lease{hk, ho}}, Some{Ls.Lease{k, o}}, got)
  +g = Pair.fst({Ls.above(k, Some{hk}) == True{} : Bool}, {Nat.is_lt(k, n) == True{} : Bool}, LSN.pl.in_bounds(q, Some{hk}, n, Ls.Waiter{k, o, True{}}, waits, a, u))
  LSN.pl.void(G, LSN.pl.ne_of_lt(hk, k, g, eq))

# a live waiter is not in a queue of dead waiters
def lu.dead_in(-G: Type, q: List<&2, Ls.Waiter>, +k: Nat, +o: Nat, d: Ls.Dead(q), i: Ls.In(Ls.Waiter{k, o, True{}}, q)) -> G:
  match q:
    case Nil{}:
      match i:
    case w <> t:
      (dw, dt) = d
      match i:
        case Inl{e}:
          LA.lease.pl.absurd(G, Equal.trans(Bool, True{}, Ls.Waiter.live(w), False{}, Equal.cong(Ls.Waiter, Bool, v => Ls.Waiter.live(v), Ls.Waiter{k, o, True{}}, w, e), dw))
        case Inr{r}:
          lu.dead_in(G, t, k, o, dt, r)

# The queue
# ---------

# a stop of k leaves alone every waiter after k
def lu.mk(+k: Nat, t: List<&2, Ls.Waiter>, a: Ls.Asc(Some{k}, t)) -> {Ls.mark(Ls.Stop{k}, t) == t : List<&2, Ls.Waiter>}:
  match t:
    case Nil{}:
      {==}
    case w <> +r:
      match w:
        case Ls.Waiter{+wk, +wo, +wl}:
          (+g, ar) = a
          %Equal.sym(Bool, Nat.is_eq(wk, k), False{}, lu.lt_ne(k, wk, g)) : {Ls.Waiter{wk, wo, Bool.and(wl, Bool.not(_))} <> Ls.mark(Ls.Stop{k}, r) == Ls.Waiter{wk, wo, wl} <> r : List<&2, Ls.Waiter>}
          %lu.and_true(wl) : {Ls.Waiter{wk, wo, Bool.and(wl, True{})} <> Ls.mark(Ls.Stop{k}, r) == Ls.Waiter{wk, wo, _} <> r : List<&2, Ls.Waiter>}
          %lu.mk(k, r, LA.pl.weaken(Some{k}, wk, r, g, ar)) : {Ls.Waiter{wk, wo, Bool.and(wl, True{})} <> Ls.mark(Ls.Stop{k}, r) == Ls.Waiter{wk, wo, Bool.and(wl, True{})} <> _ : List<&2, Ls.Waiter>}
          {==}

# when k is the first live waiter, its stop makes the grant pass it over:
# the lease goes where it goes after k
def lu.pm(q: List<&2, Ls.Waiter>, +lo: Maybe<&2, Nat>, +k: Nat, +o: Nat, +n: Nat, a: Ls.Asc(lo, q), got: {Ls.pick(q) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}) -> {Ls.L{n, Ls.pick(Ls.mark(Ls.Stop{k}, q)), Ls.after(Ls.mark(Ls.Stop{k}, q))} == Ls.L{n, Ls.pick(Ls.after(q)), Ls.after(Ls.after(q))} : Ls.L}:
  match q:
    case Nil{}:
      lu.none_some({Ls.L{n, None{}, Nil{}} == Ls.L{n, None{}, Nil{}} : Ls.L}, Ls.Lease{k, o}, got)
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, +wo, wl}:
          match wl:
            case True{}:
              (g, at) = a
              +eq = Equal.cong(Maybe<&2, Ls.Lease>, Nat, m => lu.hk(m), Some{Ls.Lease{wk, wo}}, Some{Ls.Lease{k, o}}, got)
              %lu.not_self(wk, k, eq) : {Ls.L{n, Ls.pick(Ls.Waiter{wk, wo, _} <> Ls.mark(Ls.Stop{k}, t)), Ls.after(Ls.Waiter{wk, wo, _} <> Ls.mark(Ls.Stop{k}, t))} == Ls.L{n, Ls.pick(t), Ls.after(t)} : Ls.L}
              %lu.mk(k, t, lu.asc_at(wk, k, eq, t, at)) : {Ls.L{n, Ls.pick(Ls.mark(Ls.Stop{k}, t)), Ls.after(Ls.mark(Ls.Stop{k}, t))} == Ls.L{n, Ls.pick(_), Ls.after(_)} : Ls.L}
              {==}
            case False{}:
              (g, at) = a
              lu.pm(t, Some{wk}, k, o, n, at, got)

def lu.dput(b: Bool, +wk: Nat, +wo: Nat, +wl: Bool, +k: Nat, +r: List<&2, Ls.Waiter>) -> {Ls.drop.put(b, Ls.Waiter{wk, wo, Bool.and(wl, Bool.not(Nat.is_eq(wk, k)))}, Ls.mark(Ls.Stop{k}, r)) == Ls.mark(Ls.Stop{k}, Ls.drop.put(b, Ls.Waiter{wk, wo, wl}, r)) : List<&2, Ls.Waiter>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a crash drops the same waiters whether k stopped or not
def lu.drop_mark(+p: Nat, +k: Nat, q: List<&2, Ls.Waiter>) -> {Ls.drop(Ls.Crash{p}, Ls.mark(Ls.Stop{k}, q)) == Ls.mark(Ls.Stop{k}, Ls.drop(Ls.Crash{p}, q)) : List<&2, Ls.Waiter>}:
  match q:
    case Nil{}:
      {==}
    case w <> +t:
      match w:
        case Ls.Waiter{+wk, +wo, +wl}:
          %Equal.sym(List<&2, Ls.Waiter>, Ls.drop(Ls.Crash{p}, Ls.mark(Ls.Stop{k}, t)), Ls.mark(Ls.Stop{k}, Ls.drop(Ls.Crash{p}, t)), lu.drop_mark(p, k, t)) : {Ls.drop.put(Nat.is_eq(wo, p), Ls.Waiter{wk, wo, Bool.and(wl, Bool.not(Nat.is_eq(wk, k)))}, _) == Ls.mark(Ls.Stop{k}, Ls.drop.put(Nat.is_eq(wo, p), Ls.Waiter{wk, wo, wl}, Ls.drop(Ls.Crash{p}, t))) : List<&2, Ls.Waiter>}
          lu.dput(Nat.is_eq(wo, p), wk, wo, wl, k, Ls.drop(Ls.Crash{p}, t))

# The grant
# ---------

# the free lease goes to the first live waiter, k; releasing it at once
# is stopping k before: the lease goes where it goes after k
def lu.free(+n: Nat, +k: Nat, +o: Nat, +q: List<&2, Ls.Waiter>, +lo: Maybe<&2, Nat>, a: Ls.Asc(lo, q), +got: {Ls.pick(q) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}) -> {Ls.step(Ls.L{n, Ls.pick(q), Ls.after(q)}, Ls.Release{k}) == Ls.L{n, Ls.pick(Ls.mark(Ls.Stop{k}, q)), Ls.after(Ls.mark(Ls.Stop{k}, q))} : Ls.L}:
  +rhs = {Ls.L{n, Ls.pick(Ls.mark(Ls.Stop{k}, q)), Ls.after(Ls.mark(Ls.Stop{k}, q))} : Ls.L}
  %Equal.sym(Maybe<&2, Ls.Lease>, Ls.pick(q), Some{Ls.Lease{k, o}}, got) : {Ls.release(k, n, _, Ls.after(q)) == rhs : Ls.L}
  %lu.eq_refl(k) : {Ls.release.holder(_, Ls.Lease{k, o}, k, n, Ls.after(q)) == rhs : Ls.L}
  Equal.sym(Ls.L, rhs, Ls.L{n, Ls.pick(Ls.after(q)), Ls.after(Ls.after(q))}, lu.pm(q, lo, k, o, n, a, got))

def lu.rel(hit: Bool, +hk: Nat, +ho: Nat, +j: Nat, +n: Nat, +q: List<&2, Ls.Waiter>, +k: Nat, +o: Nat, a: Ls.Asc(Some{hk}, q), u: LA.pl.Under(n, q), waits: Ls.In(Ls.Waiter{k, o, True{}}, q), got: {Ls.L.holder(Ls.release.holder(hit, Ls.Lease{hk, ho}, j, n, q)) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}) -> {Ls.step(Ls.release.holder(hit, Ls.Lease{hk, ho}, j, n, q), Ls.Release{k}) == Ls.release.holder(hit, Ls.Lease{hk, ho}, j, n, Ls.mark(Ls.Stop{k}, q)) : Ls.L}:
  match hit:
    case True{}:
      lu.free(n, k, o, q, Some{hk}, a, got)
    case False{}:
      lu.not_held({Ls.step(Ls.release.holder(False{}, Ls.Lease{hk, ho}, j, n, q), Ls.Release{k}) == Ls.release.holder(False{}, Ls.Lease{hk, ho}, j, n, Ls.mark(Ls.Stop{k}, q)) : Ls.L}, hk, ho, k, o, n, q, a, u, waits, got)

def lu.cra(hit: Bool, +hk: Nat, +ho: Nat, +p: Nat, +n: Nat, +q: List<&2, Ls.Waiter>, +k: Nat, +o: Nat, a: Ls.Asc(Some{hk}, q), u: LA.pl.Under(n, q), waits: Ls.In(Ls.Waiter{k, o, True{}}, q), got: {Ls.L.holder(Ls.settle(n, Ls.crash.put(hit, Ls.Lease{hk, ho}), Ls.drop(Ls.Crash{p}, q))) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}) -> {Ls.step(Ls.settle(n, Ls.crash.put(hit, Ls.Lease{hk, ho}), Ls.drop(Ls.Crash{p}, q)), Ls.Release{k}) == Ls.settle(n, Ls.crash.put(hit, Ls.Lease{hk, ho}), Ls.drop(Ls.Crash{p}, Ls.mark(Ls.Stop{k}, q))) : Ls.L}:
  match hit:
    case True{}:
      +d = Ls.drop(Ls.Crash{p}, q)
      %Equal.sym(List<&2, Ls.Waiter>, Ls.drop(Ls.Crash{p}, Ls.mark(Ls.Stop{k}, q)), Ls.mark(Ls.Stop{k}, d), lu.drop_mark(p, k, q)) : {Ls.step(Ls.L{n, Ls.pick(d), Ls.after(d)}, Ls.Release{k}) == Ls.L{n, Ls.pick(_), Ls.after(_)} : Ls.L}
      lu.free(n, k, o, d, Some{hk}, LA.pl.asc_drop(Ls.Crash{p}, q, Some{hk}, a), got)
    case False{}:
      lu.not_held({Ls.step(Ls.settle(n, Ls.crash.put(False{}, Ls.Lease{hk, ho}), Ls.drop(Ls.Crash{p}, q)), Ls.Release{k}) == Ls.settle(n, Ls.crash.put(False{}, Ls.Lease{hk, ho}), Ls.drop(Ls.Crash{p}, Ls.mark(Ls.Stop{k}, q))) : Ls.L}, hk, ho, k, o, n, q, a, u, waits, got)

# The law
# -------

def lu.go(+s: Ls.L, +e: Ls.Ev, +k: Nat, +o: Nat, inv: LA.pl.Inv(s), busy: Ls.Busy(s), waits: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(s)), got: {Ls.L.holder(Ls.step(s, e)) == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}) -> {Ls.step(Ls.step(s, e), Ls.Release{k}) == Ls.step(Ls.step(s, Ls.Stop{k}), e) : Ls.L}:
  match s:
    case Ls.L{+n, h, +q}:
      match h:
        case None{}:
          lu.dead_in({Ls.step(Ls.step(Ls.L{n, None{}, q}, e), Ls.Release{k}) == Ls.step(Ls.step(Ls.L{n, None{}, q}, Ls.Stop{k}), e) : Ls.L}, q, k, o, busy, waits)
        case Some{x}:
          match x:
            case Ls.Lease{+hk, +ho}:
              match e:
                case Ls.Ask{+p}:
                  (a, uh) = inv
                  (u, hu) = uh
                  lu.not_held({Ls.step(Ls.step(Ls.L{n, Some{Ls.Lease{hk, ho}}, q}, Ls.Ask{p}), Ls.Release{k}) == Ls.step(Ls.step(Ls.L{n, Some{Ls.Lease{hk, ho}}, q}, Ls.Stop{k}), Ls.Ask{p}) : Ls.L}, hk, ho, k, o, n, q, a, u, waits, got)
                case Ls.Release{+j}:
                  (a, uh) = inv
                  (u, hu) = uh
                  lu.rel(Nat.is_eq(hk, j), hk, ho, j, n, q, k, o, a, u, waits, got)
                case Ls.Stop{+j}:
                  (a, uh) = inv
                  (u, hu) = uh
                  lu.not_held({Ls.step(Ls.step(Ls.L{n, Some{Ls.Lease{hk, ho}}, q}, Ls.Stop{j}), Ls.Release{k}) == Ls.step(Ls.step(Ls.L{n, Some{Ls.Lease{hk, ho}}, q}, Ls.Stop{k}), Ls.Stop{j}) : Ls.L}, hk, ho, k, o, n, q, a, u, waits, got)
                case Ls.Crash{+p}:
                  (a, uh) = inv
                  (u, hu) = uh
                  lu.cra(Nat.is_eq(ho, p), hk, ho, p, n, q, k, o, a, u, waits, got)

def Lease.lease_undelivered_is_stopped(evs, e, k, o, waits, got):
  lu.go(Ls.run(evs), e, k, o, LA.pl.inv_run(evs), LNI.lease_never_idle(evs), waits, got)
