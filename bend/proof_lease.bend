# proof_lease: the lease laws of LAWS.bend (H6). Every event keeps an
# invariant of the reachable states: the holder came before every waiter,
# the waiters wait in arrival order, and every key is below the next one
# (`pl.Inv`). From it: first come, first served (`lease_fifo`); the lease
# is never free while a live waiter waits (`lease_never_idle`); no event
# drops a waiter it does not name (`lease_keeps_waiters`); a waiter that
# stopped waiting never holds the lease (`lease_stop_never_holds`); a
# crash frees every lease of its origin (`lease_crash_frees`).

import Base
import ./lease.bend as L

# Logic and numbers
# -----------------

def pl.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pl.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pl.BD(_, Unit, A)
  Unit{}

def pl.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pl.BD(_, A, Unit)
  Unit{}

def pl.void(-A: Type, e: Empty) -> A:
  match e:

def pl.MD(m: Maybe<&2, L.Lease>, A: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      A

def pl.none_some(-A: Type, -x: L.Lease, e: {None{} == Some{x} : Maybe<&2, L.Lease>}) -> A:
  %e : pl.MD(_, A)
  Unit{}

def pl.and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pl.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pl.eq_refl(p)

def pl.lt_irrefl(k: Nat) -> {Nat.is_lt(k, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pl.lt_irrefl(p)

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
      pl.absurdF({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+m:
      pl.lt_succ(p, m, h)

def pl.lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      pl.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      pl.absurdF({Nat.is_lt(a, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      pl.lt_trans(p, q, r, ab, bc)

def pl.lt_irrefl_at(+a: Nat, +b: Nat, eq: {a == b : Nat}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  %Equal.sym(Nat, a, b, eq) : {Nat.is_lt(_, b) == False{} : Bool}
  pl.lt_irrefl(b)

# a key below another is not it
def pl.ne_of_lt(+a: Nat, +b: Nat, lt: {Nat.is_lt(a, b) == True{} : Bool}, eq: {a == b : Nat}) -> Empty:
  pl.absurd(Empty, Equal.trans(Bool, True{}, Nat.is_lt(a, b), False{}, Equal.sym(Bool, Nat.is_lt(a, b), True{}, lt), pl.lt_irrefl_at(a, b, eq)))

# Waiters
# -------

def pl.org(w: L.Waiter) -> Nat:
  match w:
    case L.Waiter{k, o, l}:
      o

def pl.lease_of(w: L.Waiter) -> Maybe<&2, L.Lease>:
  match w:
    case L.Waiter{k, o, l}:
      Some{L.Lease{k, o}}

def pl.in_append(+x: L.Waiter, q: List<&2, L.Waiter>, +ys: List<&2, L.Waiter>, i: L.In(x, q)) -> L.In(x, List.append(&2, L.Waiter, q, ys)):
  match q:
    case Nil{}:
      match i:
    case +w <> +t:
      match i:
        case Inl{eq}:
          Inl{eq}
        case Inr{it}:
          Inr{pl.in_append(x, t, ys, it)}

def pl.in_put(b: Bool, +w: L.Waiter, +x: L.Waiter, +r: List<&2, L.Waiter>, i: L.In(x, r)) -> L.In(x, L.drop.put(b, w, r)):
  match b:
    case True{}:
      i
    case False{}:
      Inr{i}

# a waiter e does not end stays
def pl.in_drop(+e: L.Ev, q: List<&2, L.Waiter>, +x: L.Waiter, i: L.In(x, q), miss: {L.hits(e, x) == False{} : Bool}) -> L.In(x, L.drop(e, q)):
  match q:
    case Nil{}:
      match i:
    case +w <> +t:
      match i:
        case Inl{eq}:
          %eq : L.In(x, L.drop.put(L.hits(e, _), _, L.drop(e, t)))
          %Equal.sym(Bool, L.hits(e, x), False{}, miss) : L.In(x, L.drop.put(_, x, L.drop(e, t)))
          Inl{{==}}
        case Inr{it}:
          pl.in_put(L.hits(e, w), w, x, L.drop(e, t), pl.in_drop(e, t, x, it, miss))

# and stays live
def pl.in_mark(+e: L.Ev, q: List<&2, L.Waiter>, +k: Nat, +o: Nat, i: L.In(L.Waiter{k, o, True{}}, q), miss: {L.hits(e, L.Waiter{k, o, True{}}) == False{} : Bool}) -> L.In(L.Waiter{k, o, True{}}, L.mark(e, q)):
  match q:
    case Nil{}:
      match i:
    case w <> +t:
      match w:
        case L.Waiter{+wk, +wo, +wl}:
          match i:
            case Inl{+eq}:
              +ek = Equal.cong(L.Waiter, Nat, v => L.Waiter.key(v), L.Waiter{k, o, True{}}, L.Waiter{wk, wo, wl}, eq)
              +eo = Equal.cong(L.Waiter, Nat, v => pl.org(v), L.Waiter{k, o, True{}}, L.Waiter{wk, wo, wl}, eq)
              +el = Equal.cong(L.Waiter, Bool, v => L.Waiter.live(v), L.Waiter{k, o, True{}}, L.Waiter{wk, wo, wl}, eq)
              %ek : L.In(L.Waiter{k, o, True{}}, L.Waiter{_, wo, Bool.and(wl, Bool.not(L.hits(e, L.Waiter{_, wo, wl})))} <> L.mark(e, t))
              %eo : L.In(L.Waiter{k, o, True{}}, L.Waiter{k, _, Bool.and(wl, Bool.not(L.hits(e, L.Waiter{k, _, wl})))} <> L.mark(e, t))
              %el : L.In(L.Waiter{k, o, True{}}, L.Waiter{k, o, Bool.and(_, Bool.not(L.hits(e, L.Waiter{k, o, _})))} <> L.mark(e, t))
              %Equal.sym(Bool, L.hits(e, L.Waiter{k, o, True{}}), False{}, miss) : L.In(L.Waiter{k, o, True{}}, L.Waiter{k, o, Bool.and(True{}, Bool.not(_))} <> L.mark(e, t))
              Inl{{==}}
            case Inr{it}:
              Inr{pl.in_mark(e, t, k, o, it, miss)}

# Kept: no event drops a waiter it does not name
# ----------------------------------------------

def pl.pick_kept(+k: Nat, +o: Nat, +n: Nat, q: List<&2, L.Waiter>, i: L.In(L.Waiter{k, o, True{}}, q)) -> L.Kept(k, o, L.L{n, L.pick(q), L.after(q)}):
  match q:
    case Nil{}:
      match i:
    case w <> +t:
      match w:
        case L.Waiter{+wk, +wo, +wl}:
          match wl:
            case True{}:
              match i:
                case Inl{eq}:
                  Inl{Equal.sym(Maybe<&2, L.Lease>, Some{L.Lease{k, o}}, Some{L.Lease{wk, wo}}, Equal.cong(L.Waiter, Maybe<&2, L.Lease>, v => pl.lease_of(v), L.Waiter{k, o, True{}}, L.Waiter{wk, wo, True{}}, eq))}
                case Inr{it}:
                  Inr{it}
            case False{}:
              match i:
                case Inl{eq}:
                  pl.absurd(L.Kept(k, o, L.L{n, L.pick(t), L.after(t)}), Equal.cong(L.Waiter, Bool, v => L.Waiter.live(v), L.Waiter{k, o, True{}}, L.Waiter{wk, wo, False{}}, eq))
                case Inr{it}:
                  pl.pick_kept(k, o, n, t, it)

def pl.settle_kept(+k: Nat, +o: Nat, +n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, kp: Or({h == Some{L.Lease{k, o}} : Maybe<&2, L.Lease>}, L.In(L.Waiter{k, o, True{}}, q))) -> L.Kept(k, o, L.settle(n, h, q)):
  match h:
    case None{}:
      match kp:
        case Inl{e}:
          pl.none_some(L.Kept(k, o, L.settle(n, None{}, q)), L.Lease{k, o}, e)
        case Inr{i}:
          pl.pick_kept(k, o, n, q, i)
    case Some{x}:
      kp

def pl.release_kept(hit: Bool, +x: L.Lease, +j: Nat, +k: Nat, +o: Nat, +n: Nat, +q: List<&2, L.Waiter>, i: L.In(L.Waiter{k, o, True{}}, q), miss: {Nat.is_eq(k, j) == False{} : Bool}) -> L.Kept(k, o, L.release.holder(hit, x, j, n, q)):
  match hit:
    case True{}:
      pl.settle_kept(k, o, n, None{}, q, Inr{i})
    case False{}:
      Inr{pl.in_drop(L.Release{j}, q, L.Waiter{k, o, True{}}, i, miss)}

def pl.keeps_release(+j: Nat, +k: Nat, +o: Nat, +n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, i: L.In(L.Waiter{k, o, True{}}, q), miss: {Nat.is_eq(k, j) == False{} : Bool}) -> L.Kept(k, o, L.release(j, n, h, q)):
  match h:
    case None{}:
      pl.settle_kept(k, o, n, None{}, L.drop(L.Release{j}, q), Inr{pl.in_drop(L.Release{j}, q, L.Waiter{k, o, True{}}, i, miss)})
    case Some{x}:
      match x:
        case L.Lease{+hk, +ho}:
          pl.release_kept(Nat.is_eq(hk, j), L.Lease{hk, ho}, j, k, o, n, q, i, miss)

def pl.keeps(+s: L.L, +e: L.Ev, +k: Nat, +o: Nat, i: L.In(L.Waiter{k, o, True{}}, L.L.queue(s)), miss: {L.hits(e, L.Waiter{k, o, True{}}) == False{} : Bool}) -> L.Kept(k, o, L.step(s, e)):
  match s:
    case L.L{+n, h, +q}:
      match e:
        case L.Ask{p}:
          pl.settle_kept(k, o, 1n+n, h, List.append(&2, L.Waiter, q, [L.Waiter{n, p, True{}}]), Inr{pl.in_append(L.Waiter{k, o, True{}}, q, [L.Waiter{n, p, True{}}], i)})
        case L.Release{+j}:
          pl.keeps_release(j, k, o, n, h, q, i, miss)
        case L.Stop{+j}:
          Inr{pl.in_mark(L.Stop{j}, q, k, o, i, miss)}
        case L.Crash{+p}:
          pl.settle_kept(k, o, n, L.crash.holder(p, h), L.drop(L.Crash{p}, q), Inr{pl.in_drop(L.Crash{p}, q, L.Waiter{k, o, True{}}, i, miss)})

# Busy: the lease is never free while a live waiter waits
# -------------------------------------------------------

def pl.pick_busy(+n: Nat, q: List<&2, L.Waiter>) -> L.Busy(L.L{n, L.pick(q), L.after(q)}):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case L.Waiter{wk, wo, wl}:
          match wl:
            case True{}:
              Unit{}
            case False{}:
              pl.pick_busy(n, t)

def pl.settle_busy(+n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>) -> L.Busy(L.settle(n, h, q)):
  match h:
    case None{}:
      pl.pick_busy(n, q)
    case Some{x}:
      Unit{}

def pl.mark_dead(+e: L.Ev, q: List<&2, L.Waiter>, d: L.Dead(q)) -> L.Dead(L.mark(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case L.Waiter{+wk, +wo, +wl}:
          (dh, dt) = d
          %Equal.sym(Bool, wl, False{}, dh) : ({Bool.and(_, Bool.not(L.hits(e, L.Waiter{wk, wo, wl}))) == False{} : Bool} & L.Dead(L.mark(e, t)))
          ({==}, pl.mark_dead(e, t, dt))

def pl.release_busy(hit: Bool, +x: L.Lease, +j: Nat, +n: Nat, +q: List<&2, L.Waiter>) -> L.Busy(L.release.holder(hit, x, j, n, q)):
  match hit:
    case True{}:
      pl.settle_busy(n, None{}, q)
    case False{}:
      Unit{}

def pl.busy_release(+j: Nat, +n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>) -> L.Busy(L.release(j, n, h, q)):
  match h:
    case None{}:
      pl.settle_busy(n, None{}, L.drop(L.Release{j}, q))
    case Some{x}:
      match x:
        case L.Lease{+hk, +ho}:
          pl.release_busy(Nat.is_eq(hk, j), L.Lease{hk, ho}, j, n, q)

def pl.busy_stop(+j: Nat, +n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, b: L.Busy(L.L{n, h, q})) -> L.Busy(L.L{n, h, L.mark(L.Stop{j}, q)}):
  match h:
    case None{}:
      pl.mark_dead(L.Stop{j}, q, b)
    case Some{x}:
      Unit{}

def pl.busy_step(+s: L.L, +e: L.Ev, b: L.Busy(s)) -> L.Busy(L.step(s, e)):
  match s:
    case L.L{+n, h, +q}:
      match e:
        case L.Ask{p}:
          pl.settle_busy(1n+n, h, List.append(&2, L.Waiter, q, [L.Waiter{n, p, True{}}]))
        case L.Release{+j}:
          pl.busy_release(j, n, h, q)
        case L.Stop{+j}:
          pl.busy_stop(j, n, h, q, b)
        case L.Crash{+p}:
          pl.settle_busy(n, L.crash.holder(p, h), L.drop(L.Crash{p}, q))

def pl.busy_go(evs: List<&2, L.Ev>, +s: L.L, b: L.Busy(s)) -> L.Busy(L.go(evs, s)):
  match evs:
    case Nil{}:
      b
    case +e <> rest:
      pl.busy_go(rest, L.step(s, e), pl.busy_step(s, e, b))

# The invariant: arrival order, keys below the next
# -------------------------------------------------

def pl.Under(+n: Nat, q: List<&2, L.Waiter>) -> Data:
  match q:
    case Nil{}:
      Unit
    case +w <> +t:
      Sigma<&2, &2, {Nat.is_lt(L.Waiter.key(w), n) == True{} : Bool}, _ => pl.Under(n, t)>

def pl.HUnder(+n: Nat, h: Maybe<&2, L.Lease>) -> Data:
  match h:
    case None{}:
      Unit
    case Some{x}:
      match x:
        case L.Lease{hk, ho}:
          {Nat.is_lt(hk, n) == True{} : Bool}

def pl.Inv(s: L.L) -> Type:
  match s:
    case L.L{+n, +h, +q}:
      (L.Asc(L.hkey(h), q) & Sigma<&2, &2, pl.Under(n, q), _ => pl.HUnder(n, h)>)

def pl.asc_none(lo: Maybe<&2, Nat>, q: List<&2, L.Waiter>, a: L.Asc(lo, q)) -> L.Asc(None{}, q):
  match q:
    case Nil{}:
      Unit{}
    case +w <> +t:
      (_, at) = a
      ({==}, at)

# a looser bound
def pl.weaken(lo: Maybe<&2, Nat>, +l: Nat, r: List<&2, L.Waiter>, g: {L.above(l, lo) == True{} : Bool}, ar: L.Asc(Some{l}, r)) -> L.Asc(lo, r):
  match lo:
    case None{}:
      pl.asc_none(Some{l}, r, ar)
    case Some{+l0}:
      match r:
        case Nil{}:
          Unit{}
        case +w <> +t:
          (g2, at) = ar
          (pl.lt_trans(l0, l, L.Waiter.key(w), g, g2), at)

def pl.asc_put(b: Bool, +lo: Maybe<&2, Nat>, +w: L.Waiter, +r: List<&2, L.Waiter>, g: {L.above(L.Waiter.key(w), lo) == True{} : Bool}, ar: L.Asc(Some{L.Waiter.key(w)}, r)) -> L.Asc(lo, L.drop.put(b, w, r)):
  match b:
    case True{}:
      pl.weaken(lo, L.Waiter.key(w), r, g, ar)
    case False{}:
      (g, ar)

def pl.asc_drop(+e: L.Ev, q: List<&2, L.Waiter>, +lo: Maybe<&2, Nat>, a: L.Asc(lo, q)) -> L.Asc(lo, L.drop(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case +w <> +t:
      (g, at) = a
      pl.asc_put(L.hits(e, w), lo, w, L.drop(e, t), g, pl.asc_drop(e, t, Some{L.Waiter.key(w)}, at))

def pl.asc_mark(+e: L.Ev, q: List<&2, L.Waiter>, +lo: Maybe<&2, Nat>, a: L.Asc(lo, q)) -> L.Asc(lo, L.mark(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case L.Waiter{+wk, wo, wl}:
          (g, at) = a
          (g, pl.asc_mark(e, t, Some{wk}, at))

def pl.asc_snoc(q: List<&2, L.Waiter>, +lo: Maybe<&2, Nat>, +n: Nat, +o: Nat, a: L.Asc(lo, q), u: pl.Under(n, q), g: {L.above(n, lo) == True{} : Bool}) -> L.Asc(lo, List.append(&2, L.Waiter, q, [L.Waiter{n, o, True{}}])):
  match q:
    case Nil{}:
      (g, Unit{})
    case +w <> +t:
      (gw, at) = a
      (uw, ut) = u
      (gw, pl.asc_snoc(t, Some{L.Waiter.key(w)}, n, o, at, ut, uw))

def pl.under_put(b: Bool, +n: Nat, +w: L.Waiter, +r: List<&2, L.Waiter>, uw: {Nat.is_lt(L.Waiter.key(w), n) == True{} : Bool}, ur: pl.Under(n, r)) -> pl.Under(n, L.drop.put(b, w, r)):
  match b:
    case True{}:
      ur
    case False{}:
      (uw, ur)

def pl.under_drop(+e: L.Ev, q: List<&2, L.Waiter>, +n: Nat, u: pl.Under(n, q)) -> pl.Under(n, L.drop(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case +w <> +t:
      (uw, ut) = u
      pl.under_put(L.hits(e, w), n, w, L.drop(e, t), uw, pl.under_drop(e, t, n, ut))

def pl.under_mark(+e: L.Ev, q: List<&2, L.Waiter>, +n: Nat, u: pl.Under(n, q)) -> pl.Under(n, L.mark(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case L.Waiter{wk, wo, wl}:
          (uw, ut) = u
          (uw, pl.under_mark(e, t, n, ut))

def pl.under_snoc(q: List<&2, L.Waiter>, +n: Nat, +o: Nat, u: pl.Under(n, q)) -> pl.Under(1n+n, List.append(&2, L.Waiter, q, [L.Waiter{n, o, True{}}])):
  match q:
    case Nil{}:
      (pl.lt_self(n), Unit{})
    case +w <> +t:
      (uw, ut) = u
      (pl.lt_succ(L.Waiter.key(w), n, uw), pl.under_snoc(t, n, o, ut))

def pl.hunder_succ(+n: Nat, h: Maybe<&2, L.Lease>, hu: pl.HUnder(n, h)) -> pl.HUnder(1n+n, h):
  match h:
    case None{}:
      Unit{}
    case Some{x}:
      match x:
        case L.Lease{hk, ho}:
          pl.lt_succ(hk, n, hu)

def pl.h_above(+n: Nat, h: Maybe<&2, L.Lease>, hu: pl.HUnder(n, h)) -> {L.above(n, L.hkey(h)) == True{} : Bool}:
  match h:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case L.Lease{hk, ho}:
          hu

def pl.pick_inv(+n: Nat, q: List<&2, L.Waiter>, +lo: Maybe<&2, Nat>, a: L.Asc(lo, q), u: pl.Under(n, q)) -> pl.Inv(L.L{n, L.pick(q), L.after(q)}):
  match q:
    case Nil{}:
      (Unit{}, (Unit{}, Unit{}))
    case w <> +t:
      match w:
        case L.Waiter{+wk, wo, wl}:
          match wl:
            case True{}:
              (g, at) = a
              (uw, ut) = u
              (at, (ut, uw))
            case False{}:
              (g, at) = a
              (uw, ut) = u
              pl.pick_inv(n, t, Some{wk}, at, ut)

def pl.settle_inv(+n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, a: L.Asc(L.hkey(h), q), u: pl.Under(n, q), hu: pl.HUnder(n, h)) -> pl.Inv(L.settle(n, h, q)):
  match h:
    case None{}:
      pl.pick_inv(n, q, None{}, a, u)
    case Some{x}:
      (a, (u, hu))

def pl.release_inv(hit: Bool, +hk: Nat, +ho: Nat, +j: Nat, +n: Nat, +q: List<&2, L.Waiter>, a: L.Asc(Some{hk}, q), u: pl.Under(n, q), hu: {Nat.is_lt(hk, n) == True{} : Bool}) -> pl.Inv(L.release.holder(hit, L.Lease{hk, ho}, j, n, q)):
  match hit:
    case True{}:
      pl.settle_inv(n, None{}, q, pl.asc_none(Some{hk}, q, a), u, Unit{})
    case False{}:
      (pl.asc_drop(L.Release{j}, q, Some{hk}, a), (pl.under_drop(L.Release{j}, q, n, u), hu))

def pl.crash_inv(hit: Bool, +hk: Nat, +ho: Nat, +p: Nat, +n: Nat, +q: List<&2, L.Waiter>, a: L.Asc(Some{hk}, q), u: pl.Under(n, q), hu: {Nat.is_lt(hk, n) == True{} : Bool}) -> pl.Inv(L.settle(n, L.crash.put(hit, L.Lease{hk, ho}), L.drop(L.Crash{p}, q))):
  match hit:
    case True{}:
      pl.settle_inv(n, None{}, L.drop(L.Crash{p}, q), pl.asc_none(Some{hk}, L.drop(L.Crash{p}, q), pl.asc_drop(L.Crash{p}, q, Some{hk}, a)), pl.under_drop(L.Crash{p}, q, n, u), Unit{})
    case False{}:
      (pl.asc_drop(L.Crash{p}, q, Some{hk}, a), (pl.under_drop(L.Crash{p}, q, n, u), hu))

def pl.inv_ask.go(+p: Nat, +n: Nat, +h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, a: L.Asc(L.hkey(h), q), uh: Sigma<&2, &2, pl.Under(n, q), _ => pl.HUnder(n, h)>) -> pl.Inv(L.settle(1n+n, h, List.append(&2, L.Waiter, q, [L.Waiter{n, p, True{}}]))):
  (+u, +hu) = uh
  pl.settle_inv(1n+n, h, List.append(&2, L.Waiter, q, [L.Waiter{n, p, True{}}]), pl.asc_snoc(q, L.hkey(h), n, p, a, u, pl.h_above(n, h, hu)), pl.under_snoc(q, n, p, u), pl.hunder_succ(n, h, hu))

def pl.inv_ask(+p: Nat, +n: Nat, +h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, inv: pl.Inv(L.L{n, h, q})) -> pl.Inv(L.settle(1n+n, h, List.append(&2, L.Waiter, q, [L.Waiter{n, p, True{}}]))):
  (a, uh) = inv
  pl.inv_ask.go(p, n, h, q, a, uh)

def pl.inv_release(+j: Nat, +n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, inv: pl.Inv(L.L{n, h, q})) -> pl.Inv(L.release(j, n, h, q)):
  match h:
    case None{}:
      (a, uh) = inv
      (u, hu) = uh
      pl.settle_inv(n, None{}, L.drop(L.Release{j}, q), pl.asc_drop(L.Release{j}, q, None{}, a), pl.under_drop(L.Release{j}, q, n, u), Unit{})
    case Some{x}:
      match x:
        case L.Lease{+hk, +ho}:
          (a, uh) = inv
          (u, hu) = uh
          pl.release_inv(Nat.is_eq(hk, j), hk, ho, j, n, q, a, u, hu)

def pl.inv_stop(+j: Nat, +n: Nat, +h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, inv: pl.Inv(L.L{n, h, q})) -> pl.Inv(L.L{n, h, L.mark(L.Stop{j}, q)}):
  (a, uh) = inv
  (u, hu) = uh
  (pl.asc_mark(L.Stop{j}, q, L.hkey(h), a), (pl.under_mark(L.Stop{j}, q, n, u), hu))

def pl.inv_crash(+p: Nat, +n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, inv: pl.Inv(L.L{n, h, q})) -> pl.Inv(L.settle(n, L.crash.holder(p, h), L.drop(L.Crash{p}, q))):
  match h:
    case None{}:
      (a, uh) = inv
      (u, hu) = uh
      pl.settle_inv(n, None{}, L.drop(L.Crash{p}, q), pl.asc_drop(L.Crash{p}, q, None{}, a), pl.under_drop(L.Crash{p}, q, n, u), Unit{})
    case Some{x}:
      match x:
        case L.Lease{+hk, +ho}:
          (a, uh) = inv
          (u, hu) = uh
          pl.crash_inv(Nat.is_eq(ho, p), hk, ho, p, n, q, a, u, hu)

def pl.inv_step(+s: L.L, +e: L.Ev, inv: pl.Inv(s)) -> pl.Inv(L.step(s, e)):
  match s:
    case L.L{+n, +h, +q}:
      match e:
        case L.Ask{+p}:
          pl.inv_ask(p, n, h, q, inv)
        case L.Release{+j}:
          pl.inv_release(j, n, h, q, inv)
        case L.Stop{+j}:
          pl.inv_stop(j, n, h, q, inv)
        case L.Crash{+p}:
          pl.inv_crash(p, n, h, q, inv)

def pl.inv_go(evs: List<&2, L.Ev>, +s: L.L, inv: pl.Inv(s)) -> pl.Inv(L.go(evs, s)):
  match evs:
    case Nil{}:
      inv
    case +e <> rest:
      pl.inv_go(rest, L.step(s, e), pl.inv_step(s, e, inv))

def pl.inv_run(+evs: List<&2, L.Ev>) -> pl.Inv(L.run(evs)):
  pl.inv_go(evs, L.L.empty(), (Unit{}, (Unit{}, Unit{})))

def pl.inv_fifo(+s: L.L, inv: pl.Inv(s)) -> L.Fifo(s):
  match s:
    case L.L{n, h, q}:
      (a, _) = inv
      a

def pl.bounds_up(+l: Nat, +kw: Nat, +kx: Nat, +n: Nat, g: {Nat.is_lt(l, kw) == True{} : Bool}, p: ({Nat.is_lt(kw, kx) == True{} : Bool} & {Nat.is_lt(kx, n) == True{} : Bool})) -> ({Nat.is_lt(l, kx) == True{} : Bool} & {Nat.is_lt(kx, n) == True{} : Bool}):
  (ab, ltn) = p
  (pl.lt_trans(l, kw, kx, g, ab), ltn)

# a waiter is above the bound of its queue, and below the next key
def pl.in_bounds(q: List<&2, L.Waiter>, +lo: Maybe<&2, Nat>, +n: Nat, +x: L.Waiter, i: L.In(x, q), a: L.Asc(lo, q), u: pl.Under(n, q)) -> ({L.above(L.Waiter.key(x), lo) == True{} : Bool} & {Nat.is_lt(L.Waiter.key(x), n) == True{} : Bool}):
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
              %Equal.sym(L.Waiter, x, w, eq) : ({True{} == True{} : Bool} & {Nat.is_lt(L.Waiter.key(_), n) == True{} : Bool})
              ({==}, uw)
            case Inr{it}:
              (g, at) = a
              (uw, ut) = u
              ({==}, Pair.snd({L.above(L.Waiter.key(x), Some{L.Waiter.key(w)}) == True{} : Bool}, {Nat.is_lt(L.Waiter.key(x), n) == True{} : Bool}, pl.in_bounds(t, Some{L.Waiter.key(w)}, n, x, it, at, ut)))
        case Some{+l}:
          match i:
            case Inl{eq}:
              (g, at) = a
              (uw, ut) = u
              %Equal.sym(L.Waiter, x, w, eq) : ({Nat.is_lt(l, L.Waiter.key(_)) == True{} : Bool} & {Nat.is_lt(L.Waiter.key(_), n) == True{} : Bool})
              (g, uw)
            case Inr{it}:
              (g, at) = a
              (uw, ut) = u
              pl.bounds_up(l, L.Waiter.key(w), L.Waiter.key(x), n, g, pl.in_bounds(t, Some{L.Waiter.key(w)}, n, x, it, at, ut))

# A stopped waiter never holds
# ----------------------------

# no live waiter of q has key k
def pl.NoLive(+k: Nat, q: List<&2, L.Waiter>) -> Type:
  match q:
    case Nil{}:
      Unit
    case +w <> +t:
      (({L.Waiter.key(w) == k : Nat} -> {L.Waiter.live(w) == False{} : Bool}) & pl.NoLive(k, t))

# k neither holds nor waits live, and every new key is above it
def pl.Gone(+k: Nat, s: L.L) -> Type:
  match s:
    case L.L{+n, +h, +q}:
      (L.NotHeld(k, h) & (pl.NoLive(k, q) & {Nat.is_lt(k, n) == True{} : Bool}))

def pl.kill(+wk: Nat, +k: Nat, +wl: Bool, eq: {wk == k : Nat}) -> {Bool.and(wl, Bool.not(Nat.is_eq(wk, k))) == False{} : Bool}:
  %Equal.sym(Nat, wk, k, eq) : {Bool.and(wl, Bool.not(Nat.is_eq(_, k))) == False{} : Bool}
  %pl.eq_refl(k) : {Bool.and(wl, Bool.not(_)) == False{} : Bool}
  pl.and_false(wl)

# a stop of k leaves no live waiter of k
def pl.mark_kills(+k: Nat, q: List<&2, L.Waiter>) -> pl.NoLive(k, L.mark(L.Stop{k}, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case L.Waiter{+wk, +wo, +wl}:
          (eq => pl.kill(wk, k, wl, eq), pl.mark_kills(k, t))

def pl.dead_and(+wl: Bool, +x: Bool, f: {wl == False{} : Bool}) -> {Bool.and(wl, x) == False{} : Bool}:
  %Equal.sym(Bool, wl, False{}, f) : {Bool.and(_, x) == False{} : Bool}
  {==}

def pl.nolive_mark(+e: L.Ev, +k: Nat, q: List<&2, L.Waiter>, nl: pl.NoLive(k, q)) -> pl.NoLive(k, L.mark(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case L.Waiter{+wk, +wo, +wl}:
          (f, nt) = nl
          (eq => pl.dead_and(wl, Bool.not(L.hits(e, L.Waiter{wk, wo, wl})), f(eq)), pl.nolive_mark(e, k, t, nt))

def pl.nolive_put(b: Bool, +k: Nat, +w: L.Waiter, +r: List<&2, L.Waiter>, f: {L.Waiter.key(w) == k : Nat} -> {L.Waiter.live(w) == False{} : Bool}, nr: pl.NoLive(k, r)) -> pl.NoLive(k, L.drop.put(b, w, r)):
  match b:
    case True{}:
      nr
    case False{}:
      (f, nr)

def pl.nolive_drop(+e: L.Ev, +k: Nat, q: List<&2, L.Waiter>, nl: pl.NoLive(k, q)) -> pl.NoLive(k, L.drop(e, q)):
  match q:
    case Nil{}:
      Unit{}
    case +w <> +t:
      (f, nt) = nl
      pl.nolive_put(L.hits(e, w), k, w, L.drop(e, t), f, pl.nolive_drop(e, k, t, nt))

def pl.fresh(+k: Nat, +n: Nat, lt: {Nat.is_lt(k, n) == True{} : Bool}, eq: {n == k : Nat}) -> {True{} == False{} : Bool}:
  pl.void({True{} == False{} : Bool}, pl.ne_of_lt(k, n, lt, Equal.sym(Nat, n, k, eq)))

def pl.nolive_snoc(+k: Nat, +n: Nat, +o: Nat, q: List<&2, L.Waiter>, nl: pl.NoLive(k, q), lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.NoLive(k, List.append(&2, L.Waiter, q, [L.Waiter{n, o, True{}}])):
  match q:
    case Nil{}:
      (eq => pl.fresh(k, n, lt, eq), Unit{})
    case +w <> +t:
      (f, nt) = nl
      (f, pl.nolive_snoc(k, n, o, t, nt, lt))

def pl.pick_gone(+k: Nat, +n: Nat, q: List<&2, L.Waiter>, nl: pl.NoLive(k, q), lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.Gone(k, L.L{n, L.pick(q), L.after(q)}):
  match q:
    case Nil{}:
      (Unit{}, (Unit{}, lt))
    case w <> +t:
      match w:
        case L.Waiter{wk, wo, wl}:
          match wl:
            case True{}:
              (f, nt) = nl
              (eq => pl.absurd(Empty, f(eq)), (nt, lt))
            case False{}:
              (f, nt) = nl
              pl.pick_gone(k, n, t, nt, lt)

def pl.settle_gone(+k: Nat, +n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, nh: L.NotHeld(k, h), nl: pl.NoLive(k, q), lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.Gone(k, L.settle(n, h, q)):
  match h:
    case None{}:
      pl.pick_gone(k, n, q, nl, lt)
    case Some{x}:
      (nh, (nl, lt))

def pl.release_gone(hit: Bool, +hk: Nat, +ho: Nat, +j: Nat, +k: Nat, +n: Nat, +q: List<&2, L.Waiter>, nh: L.NotHeld(k, Some{L.Lease{hk, ho}}), nl: pl.NoLive(k, q), lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.Gone(k, L.release.holder(hit, L.Lease{hk, ho}, j, n, q)):
  match hit:
    case True{}:
      pl.settle_gone(k, n, None{}, q, Unit{}, nl, lt)
    case False{}:
      (nh, (pl.nolive_drop(L.Release{j}, k, q, nl), lt))

def pl.crash_gone(hit: Bool, +hk: Nat, +ho: Nat, +k: Nat, nh: L.NotHeld(k, Some{L.Lease{hk, ho}})) -> L.NotHeld(k, L.crash.put(hit, L.Lease{hk, ho})):
  match hit:
    case True{}:
      Unit{}
    case False{}:
      nh

def pl.crash_notheld(+p: Nat, +k: Nat, h: Maybe<&2, L.Lease>, nh: L.NotHeld(k, h)) -> L.NotHeld(k, L.crash.holder(p, h)):
  match h:
    case None{}:
      Unit{}
    case Some{x}:
      match x:
        case L.Lease{+hk, +ho}:
          pl.crash_gone(Nat.is_eq(ho, p), hk, ho, k, nh)

def pl.gone_release(+j: Nat, +k: Nat, +n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, g: pl.Gone(k, L.L{n, h, q})) -> pl.Gone(k, L.release(j, n, h, q)):
  match h:
    case None{}:
      (nh, rest) = g
      (nl, lt) = rest
      pl.settle_gone(k, n, None{}, L.drop(L.Release{j}, q), Unit{}, pl.nolive_drop(L.Release{j}, k, q, nl), lt)
    case Some{x}:
      match x:
        case L.Lease{+hk, +ho}:
          (nh, rest) = g
          (nl, lt) = rest
          pl.release_gone(Nat.is_eq(hk, j), hk, ho, j, k, n, q, nh, nl, lt)

def pl.gone_ask(+k: Nat, +n: Nat, +p: Nat, +h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, nh: L.NotHeld(k, h), nl: pl.NoLive(k, q), +lt: {Nat.is_lt(k, n) == True{} : Bool}) -> pl.Gone(k, L.settle(1n+n, h, List.append(&2, L.Waiter, q, [L.Waiter{n, p, True{}}]))):
  pl.settle_gone(k, 1n+n, h, List.append(&2, L.Waiter, q, [L.Waiter{n, p, True{}}]), nh, pl.nolive_snoc(k, n, p, q, nl, lt), pl.lt_succ(k, n, lt))

def pl.gone_step(+k: Nat, +s: L.L, +e: L.Ev, g: pl.Gone(k, s)) -> pl.Gone(k, L.step(s, e)):
  match s:
    case L.L{+n, +h, +q}:
      match e:
        case L.Ask{+p}:
          (nh, rest) = g
          (nl, lt) = rest
          pl.gone_ask(k, n, p, h, q, nh, nl, lt)
        case L.Release{+j}:
          pl.gone_release(j, k, n, h, q, g)
        case L.Stop{+j}:
          (nh, rest) = g
          (nl, lt) = rest
          (nh, (pl.nolive_mark(L.Stop{j}, k, q, nl), lt))
        case L.Crash{+p}:
          (nh, rest) = g
          (nl, lt) = rest
          pl.settle_gone(k, n, L.crash.holder(p, h), L.drop(L.Crash{p}, q), pl.crash_notheld(p, k, h, nh), pl.nolive_drop(L.Crash{p}, k, q, nl), lt)

def pl.gone_go(+k: Nat, evs: List<&2, L.Ev>, +s: L.L, g: pl.Gone(k, s)) -> pl.Gone(k, L.go(evs, s)):
  match evs:
    case Nil{}:
      g
    case +e <> rest:
      pl.gone_go(k, rest, L.step(s, e), pl.gone_step(k, s, e, g))

def pl.gone_holder(h: Maybe<&2, L.Lease>, +k: Nat, ab: {L.above(k, L.hkey(h)) == True{} : Bool}) -> L.NotHeld(k, h):
  match h:
    case None{}:
      Unit{}
    case Some{x}:
      match x:
        case L.Lease{+hk, ho}:
          eq => pl.ne_of_lt(hk, k, ab, eq)

def pl.gone_of(h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, +k: Nat, +n: Nat, p: ({L.above(k, L.hkey(h)) == True{} : Bool} & {Nat.is_lt(k, n) == True{} : Bool})) -> pl.Gone(k, L.L{n, h, L.mark(L.Stop{k}, q)}):
  (ab, lt) = p
  (pl.gone_holder(h, k, ab), (pl.mark_kills(k, q), lt))

# a stop of a live waiter makes it gone
def pl.gone_start(+s: L.L, +k: Nat, +o: Nat, inv: pl.Inv(s), i: L.In(L.Waiter{k, o, True{}}, L.L.queue(s))) -> pl.Gone(k, L.step(s, L.Stop{k})):
  match s:
    case L.L{+n, +h, +q}:
      (a, uh) = inv
      (u, hu) = uh
      pl.gone_of(h, q, k, n, pl.in_bounds(q, L.hkey(h), n, L.Waiter{k, o, True{}}, i, a, u))

def pl.gone_held(+k: Nat, +s: L.L, g: pl.Gone(k, s)) -> L.NotHeld(k, L.L.holder(s)):
  match s:
    case L.L{n, h, q}:
      (nh, _) = g
      nh

# A crash frees its origin
# ------------------------

def pl.none_put(+p: Nat, +wk: Nat, +wo: Nat, +wl: Bool, b: Bool, eb: {Nat.is_eq(wo, p) == b : Bool}, +r: List<&2, L.Waiter>, nr: L.NoneFrom(p, r)) -> L.NoneFrom(p, L.drop.put(b, L.Waiter{wk, wo, wl}, r)):
  match b:
    case True{}:
      nr
    case False{}:
      (eb, nr)

def pl.none_drop(+p: Nat, q: List<&2, L.Waiter>) -> L.NoneFrom(p, L.drop(L.Crash{p}, q)):
  match q:
    case Nil{}:
      Unit{}
    case w <> +t:
      match w:
        case L.Waiter{+wk, +wo, +wl}:
          pl.none_put(p, wk, wo, wl, Nat.is_eq(wo, p), {==}, L.drop(L.Crash{p}, t), pl.none_drop(p, t))

def pl.pick_freed(+p: Nat, +n: Nat, q: List<&2, L.Waiter>, nf: L.NoneFrom(p, q)) -> L.Freed(p, L.L{n, L.pick(q), L.after(q)}):
  match q:
    case Nil{}:
      (Unit{}, Unit{})
    case w <> +t:
      match w:
        case L.Waiter{wk, wo, wl}:
          match wl:
            case True{}:
              nf
            case False{}:
              (e, nt) = nf
              pl.pick_freed(p, n, t, nt)

def pl.crash_put(+p: Nat, b: Bool, +hk: Nat, +ho: Nat, eb: {Nat.is_eq(ho, p) == b : Bool}) -> L.NotFrom(p, L.crash.put(b, L.Lease{hk, ho})):
  match b:
    case True{}:
      Unit{}
    case False{}:
      eb

def pl.crash_holder(+p: Nat, h: Maybe<&2, L.Lease>) -> L.NotFrom(p, L.crash.holder(p, h)):
  match h:
    case None{}:
      Unit{}
    case Some{x}:
      match x:
        case L.Lease{+hk, +ho}:
          pl.crash_put(p, Nat.is_eq(ho, p), hk, ho, {==})

def pl.settle_freed(+p: Nat, +n: Nat, h: Maybe<&2, L.Lease>, +q: List<&2, L.Waiter>, nh: L.NotFrom(p, h), nq: L.NoneFrom(p, q)) -> L.Freed(p, L.settle(n, h, q)):
  match h:
    case None{}:
      pl.pick_freed(p, n, q, nq)
    case Some{x}:
      (nh, nq)

# The laws
# --------

def lease_fifo(+evs: List<&2, L.Ev>) -> L.Fifo(L.run(evs)):
  pl.inv_fifo(L.run(evs), pl.inv_run(evs))

def lease_never_idle(+evs: List<&2, L.Ev>) -> L.Busy(L.run(evs)):
  pl.busy_go(evs, L.L.empty(), Unit{})

def lease_keeps_waiters(+s: L.L, +e: L.Ev, +k: Nat, +o: Nat, waits: L.In(L.Waiter{k, o, True{}}, L.L.queue(s)), other: {L.hits(e, L.Waiter{k, o, True{}}) == False{} : Bool}) -> L.Kept(k, o, L.step(s, e)):
  pl.keeps(s, e, k, o, waits, other)

def lease_stop_never_holds(+evs: List<&2, L.Ev>, +k: Nat, +o: Nat, +rest: List<&2, L.Ev>, waits: L.In(L.Waiter{k, o, True{}}, L.L.queue(L.run(evs)))) -> L.NotHeld(k, L.L.holder(L.go(rest, L.step(L.run(evs), L.Stop{k})))):
  +s = L.step(L.run(evs), L.Stop{k})
  pl.gone_held(k, L.go(rest, s), pl.gone_go(k, rest, s, pl.gone_start(L.run(evs), k, o, pl.inv_run(evs), waits)))

def lease_crash_frees(+s: L.L, +p: Nat) -> L.Freed(p, L.step(s, L.Crash{p})):
  match s:
    case L.L{+n, h, +q}:
      pl.settle_freed(p, n, L.crash.holder(p, h), L.drop(L.Crash{p}, q), pl.crash_holder(p, h), pl.none_drop(p, q))
