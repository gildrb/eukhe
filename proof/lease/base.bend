# eukhe: lemmas the proofs of area lease share

import Base
import ../../bend/lease.bend as Ls
import ../../bend/ffi_lease.bend as FLs
import ../../bend/wire.bend as Wr
import ../../laws/lease.bend as Lease
import ../base/wire.bend as LWire

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

# The entry (bend/ffi_lease.bend)
# -------------------------------
# The entry reads every input as the laws' reader does (`le.read`); a
# read event moves the lease by the model's step and its reply is the
# laws' spelling (`le.reply`): the model's grant, keys and ended keys are
# the laws' (`le.grant`, `le.keys`, `le.ended`).

def le.and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def le.and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      lease.pl.absurdF({b == True{} : Bool}, h)

def le.MD(m: Maybe<&2, Ls.Ev>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def le.none_some(-A: Type, -e: Ls.Ev, h: {None{} == Some{e} : Maybe<&2, Ls.Ev>}) -> A:
  %h : le.MD(_, A)
  Unit{}

def le.get(m: Maybe<&2, Ls.Ev>, d: Ls.Ev) -> Ls.Ev:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def le.some_inj(+a: Ls.Ev, +b: Ls.Ev, h: {Some{a} == Some{b} : Maybe<&2, Ls.Ev>}) -> {a == b : Ls.Ev}:
  Equal.cong(Maybe<&2, Ls.Ev>, Ls.Ev, m => le.get(m, a), Some{a}, Some{b}, h)

# Reading

def le.ask(d: Wr.Dec<Nat>) -> {Lease.lw_read.ev(d, 0n) == FLs.get_ev.ask(d) : Wr.Dec<Ls.Ev>}:
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def le.release(d: Wr.Dec<Nat>) -> {Lease.lw_read.ev(d, 1n) == FLs.get_ev.release(d) : Wr.Dec<Ls.Ev>}:
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def le.crash(d: Wr.Dec<Nat>) -> {Lease.lw_read.ev(d, 2n) == FLs.get_ev.crash(d) : Wr.Dec<Ls.Ev>}:
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def le.other(d: Wr.Dec<Nat>, p: Nat) -> {Lease.lw_read.ev(d, 3n+p) == Wr.Bad{} : Wr.Dec<Ls.Ev>}:
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def le.tag(t: Nat, +s: String) -> {Lease.lw_read.ev(Wr.get_nat(s), t) == FLs.get_ev.tag(t, s) : Wr.Dec<Ls.Ev>}:
  match t:
    case 0n:
      le.ask(Wr.get_nat(s))
    case 1n:
      le.release(Wr.get_nat(s))
    case 2n:
      le.crash(Wr.get_nat(s))
    case 3n+p:
      le.other(Wr.get_nat(s), p)

# the entry reads every input as the laws' reader does
def le.read(r: Wr.Dec<Nat>) -> {Lease.lw_read.go(r) == FLs.get_ev.go(r) : Wr.Dec<Ls.Ev>}:
  match r:
    case Wr.Got{t, s}:
      le.tag(t, s)
    case Wr.Bad{}:
      {==}

# The reply

def le.put_grant(m: Maybe<&2, Nat>, rest: String) -> {FLs.put_grant(m, rest) == Lease.lw_spell_grant(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{k}:
      {==}

def le.grant_new(b: Bool, k: Nat) -> {Ls.grant.new(b, k) == Lease.lw_grant.new(b, k) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def le.grant_held(+j: Nat, h2: Maybe<&2, Ls.Lease>) -> {Ls.grant.held(j, h2) == Lease.lw_grant(Ls.hkey(h2), Some{j}) : Maybe<&2, Nat>}:
  match h2:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Ls.Lease{+k, o}:
          le.grant_new(Nat.is_eq(j, k), k)

def le.grant_free(h2: Maybe<&2, Ls.Lease>) -> {Ls.grant.free(h2) == Lease.lw_grant(Ls.hkey(h2), None{}) : Maybe<&2, Nat>}:
  match h2:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Ls.Lease{k, o}:
          {==}

# the model's grant is the laws'
def le.grant(h: Maybe<&2, Ls.Lease>, +h2: Maybe<&2, Ls.Lease>) -> {Ls.grant(h, h2) == Lease.lw_grant(Ls.hkey(h2), Ls.hkey(h)) : Maybe<&2, Nat>}:
  match h:
    case None{}:
      le.grant_free(h2)
    case Some{y}:
      match y:
        case Ls.Lease{j, p}:
          le.grant_held(j, h2)

def le.keys_queue(q: List<&2, Ls.Waiter>) -> {Ls.keys.queue(q) == Lease.lw_keys.queue(q) : List<&2, Nat>}:
  match q:
    case Nil{}:
      {==}
    case w <> t:
      match w:
        case Ls.Waiter{k, o, l}:
          %le.keys_queue(t) : {k <> Ls.keys.queue(t) == k <> _ : List<&2, Nat>}
          {==}

# the model's keys are the laws'
def le.keys(s: Ls.L) -> {Ls.keys(s) == Lease.lw_keys(s) : List<&2, Nat>}:
  match s:
    case Ls.L{n, h, q}:
      match h:
        case None{}:
          le.keys_queue(q)
        case Some{x}:
          match x:
            case Ls.Lease{k, o}:
              %le.keys_queue(q) : {k <> Ls.keys.queue(q) == k <> _ : List<&2, Nat>}
              {==}

def le.has(+k: Nat, ks: List<&2, Nat>) -> {Ls.has(k, ks) == Lease.lw_in(k, ks) : Bool}:
  match ks:
    case Nil{}:
      {==}
    case j <> t:
      %le.has(k, t) : {Bool.or(Nat.is_eq(j, k), Ls.has(k, t)) == Bool.or(Nat.is_eq(j, k), _) : Bool}
      {==}

def le.ended_put(b: Bool, k: Nat, r: List<&2, Nat>) -> {Ls.ended.put(Bool.not(b), k, r) == Lease.lw_ended.put(b, k, r) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's ended keys are the laws'
def le.ended(+kept: List<&2, Nat>, ks: List<&2, Nat>) -> {Ls.ended(kept, ks) == Lease.lw_ended(kept, ks) : List<&2, Nat>}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +t:
      %le.ended(kept, t) : {Ls.ended.put(Bool.not(Ls.has(k, kept)), k, Ls.ended(kept, t)) == Lease.lw_ended.put(Lease.lw_in(k, kept), k, _) : List<&2, Nat>}
      %le.has(k, kept) : {Ls.ended.put(Bool.not(Ls.has(k, kept)), k, Ls.ended(kept, t)) == Lease.lw_ended.put(_, k, Ls.ended(kept, t)) : List<&2, Nat>}
      le.ended_put(Ls.has(k, kept), k, Ls.ended(kept, t))

# what the entry spells for the model's answer is the laws' answer
def le.answer(+s: Ls.L, +s2: Ls.L) -> {FLs.put_answer(Ls.Answer{Ls.grant(Ls.L.holder(s), Ls.L.holder(s2)), Ls.ended(Ls.keys(s2), Ls.keys(s))}) == Lease.lw_answer(s, s2) : String}:
  +g = Ls.grant(Ls.L.holder(s), Ls.L.holder(s2))
  +d = Ls.ended(Ls.keys(s2), Ls.keys(s))
  %le.grant(Ls.L.holder(s), Ls.L.holder(s2)) : {FLs.put_grant(g, Wr.put_list(~Nat, ~Wr.put_nat, d, "")) == Lease.lw_spell_grant(_, Wr.put_list(~Nat, ~Wr.put_nat, Lease.lw_ended(Lease.lw_keys(s2), Lease.lw_keys(s)), "")) : String}
  %le.keys(s2) : {FLs.put_grant(g, Wr.put_list(~Nat, ~Wr.put_nat, d, "")) == Lease.lw_spell_grant(g, Wr.put_list(~Nat, ~Wr.put_nat, Lease.lw_ended(_, Lease.lw_keys(s)), "")) : String}
  %le.keys(s) : {FLs.put_grant(g, Wr.put_list(~Nat, ~Wr.put_nat, d, "")) == Lease.lw_spell_grant(g, Wr.put_list(~Nat, ~Wr.put_nat, Lease.lw_ended(Ls.keys(s2), _), "")) : String}
  %le.ended(Ls.keys(s2), Ls.keys(s)) : {FLs.put_grant(g, Wr.put_list(~Nat, ~Wr.put_nat, d, "")) == Lease.lw_spell_grant(g, Wr.put_list(~Nat, ~Wr.put_nat, _, "")) : String}
  le.put_grant(g, Wr.put_list(~Nat, ~Wr.put_nat, d, ""))

# a read event: the model's step, the laws' reply
def le.reply(+s: Ls.L, +e: Ls.Ev) -> {FLs.step.reply(e, Ls.L.next(s), Ls.answer(s, e)) == (FLs.Live{Ls.step(s, e)}, Lease.lw_reply(s, e)) : FLs.St & String}:
  match e:
    case Ls.Ask{+o}:
      +s2 = Ls.step(s, Ls.Ask{o})
      %le.answer(s, s2) : {FLs.step.reply(Ls.Ask{o}, Ls.L.next(s), Ls.answer(s, Ls.Ask{o})) == (FLs.Live{s2}, Wr.put_nat(Ls.L.next(s), _)) : FLs.St & String}
      {==}
    case Ls.Release{+k}:
      +s2 = Ls.step(s, Ls.Release{k})
      %le.answer(s, s2) : {FLs.step.reply(Ls.Release{k}, Ls.L.next(s), Ls.answer(s, Ls.Release{k})) == (FLs.Live{s2}, _) : FLs.St & String}
      {==}
    case Ls.Stop{+k}:
      +s2 = Ls.step(s, Ls.Stop{k})
      %le.answer(s, s2) : {FLs.step.reply(Ls.Stop{k}, Ls.L.next(s), Ls.answer(s, Ls.Stop{k})) == (FLs.Live{s2}, _) : FLs.St & String}
      {==}
    case Ls.Crash{+o}:
      +s2 = Ls.step(s, Ls.Crash{o})
      %le.answer(s, s2) : {FLs.step.reply(Ls.Crash{o}, Ls.L.next(s), Ls.answer(s, Ls.Crash{o})) == (FLs.Live{s2}, _) : FLs.St & String}
      {==}

# an event the laws' reader reads whole steps the entry as the model
def le.got(+s: Ls.L, d: Wr.Dec<Ls.Ev>, +e: Ls.Ev, got: {Lease.lw_read.whole(d) == Some{e} : Maybe<&2, Ls.Ev>}) -> {FLs.step.ev(s, d) == (FLs.Live{Ls.step(s, e)}, Lease.lw_reply(s, e)) : FLs.St & String}:
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          %le.some_inj(x, e, got) : {FLs.step.end(True{}, s, x) == (FLs.Live{Ls.step(s, _)}, Lease.lw_reply(s, _)) : FLs.St & String}
          le.reply(s, x)
        case SCon{c, t}:
          le.none_some({(FLs.Live{s}, FLs.fail()) == (FLs.Live{Ls.step(s, e)}, Lease.lw_reply(s, e)) : FLs.St & String}, e, got)
    case Wr.Bad{}:
      le.none_some({(FLs.Live{s}, FLs.fail()) == (FLs.Live{Ls.step(s, e)}, Lease.lw_reply(s, e)) : FLs.St & String}, e, got)

# an input the laws' reader reads whole steps the entry as the model
def le.reads(+s: Ls.L, +i: String, +e: Ls.Ev, got: {Lease.lw_read(i) == Some{e} : Maybe<&2, Ls.Ev>}) -> {FLs.step(FLs.Live{s}, i) == (FLs.Live{Ls.step(s, e)}, Lease.lw_reply(s, e)) : FLs.St & String}:
  %le.read(Wr.get_nat(i)) : {FLs.step.ev(s, _) == (FLs.Live{Ls.step(s, e)}, Lease.lw_reply(s, e)) : FLs.St & String}
  le.got(s, Lease.lw_read.go(Wr.get_nat(i)), e, got)

# the laws' reader reads back every event the owner spells
def le.rt(+e: Ls.Ev, fits: {Lease.lw_fits(e) == True{} : Bool}) -> {Lease.lw_read(Lease.lw_spell_ev(e)) == Some{e} : Maybe<&2, Ls.Ev>}:
  match e:
    case Ls.Ask{+o}:
      %LWire.pw6.nat(o, "", fits) : {Lease.lw_read.whole(Lease.lw_read.ev(_, 0n)) == Some{Ls.Ask{o}} : Maybe<&2, Ls.Ev>}
      {==}
    case Ls.Release{+k}:
      %LWire.pw6.nat(k, "", fits) : {Lease.lw_read.whole(Lease.lw_read.ev(_, 1n)) == Some{Ls.Release{k}} : Maybe<&2, Ls.Ev>}
      {==}
    case Ls.Stop{k}:
      lease.pl.absurdF({Lease.lw_read(Lease.lw_spell_ev(Ls.Stop{k})) == Some{Ls.Stop{k}} : Maybe<&2, Ls.Ev>}, fits)
    case Ls.Crash{+o}:
      %LWire.pw6.nat(o, "", fits) : {Lease.lw_read.whole(Lease.lw_read.ev(_, 2n)) == Some{Ls.Crash{o}} : Maybe<&2, Ls.Ev>}
      {==}

# every event the owner sends steps the entry as the model
def le.answers(+s: Ls.L, +e: Ls.Ev, fits: {Lease.lw_fits(e) == True{} : Bool}) -> {FLs.step(FLs.Live{s}, Lease.lw_spell_ev(e)) == (FLs.Live{Ls.step(s, e)}, Lease.lw_reply(s, e)) : FLs.St & String}:
  le.reads(s, Lease.lw_spell_ev(e), e, le.rt(e, fits))
