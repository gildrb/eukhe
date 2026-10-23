# eukhe: the proof of LAW failover_base_saturation_exact

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_le.bend as LNatIsLe
import ./base.bend as LA

# Saturated base
# --------------

def rx.flip_le(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n b:
      LBoolMisc.rp.absurdT({Nat.is_le(b, 0n) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(0n, b), False{}, Equal.sym(Bool, Nat.is_le(0n, b), True{}, LNatIsLe.rp.le_zero(b)), e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rx.flip_le(p, q, e)

# a base at or past m doubles to m, capped at m
def rx.sat_m(+r: Nat, +x: Nat, +m: Nat, h: {Nat.is_le(m, x) == True{} : Bool}) -> {Nat.min(Retry.rs.twice(r, x), m) == m : Nat}:
  LA.rx.min_r(Retry.rs.twice(r, x), m, LA.rx.le_trans(m, x, Retry.rs.twice(r, x), h, LA.rx.twice_ge(r, x)))

def rx.base_sat(le: Bool, +r: Nat, +b: Nat, +m: Nat, +c: Nat, e: {Nat.is_le(b, c) == le : Bool}, +h: {Nat.is_le(m, c) == True{} : Bool}) -> {Nat.min(Retry.rs.twice(r, Nat.min(b, c)), m) == Nat.min(Retry.rs.twice(r, b), m) : Nat}:
  match le:
    case True{}:
      %Equal.sym(Nat, Nat.min(b, c), b, LA.rx.min_l(b, c, e)) : {Nat.min(Retry.rs.twice(r, _), m) == Nat.min(Retry.rs.twice(r, b), m) : Nat}
      {==}
    case False{}:
      +cb = rx.flip_le(b, c, e)
      %Equal.sym(Nat, Nat.min(b, c), c, LA.rx.min_r(b, c, cb)) : {Nat.min(Retry.rs.twice(r, _), m) == Nat.min(Retry.rs.twice(r, b), m) : Nat}
      Equal.trans(Nat, Nat.min(Retry.rs.twice(r, c), m), m, Nat.min(Retry.rs.twice(r, b), m), rx.sat_m(r, c, m, h), Equal.sym(Nat, Nat.min(Retry.rs.twice(r, b), m), m, rx.sat_m(r, b, m, LA.rx.le_trans(m, c, b, h, cb))))

def rx.bs_mode(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +s: Nat, +b1: Nat, +b2: Nat, +m: Nat, e: {R.double(Nat.sub(R.length(ts), len), b1, m) == R.double(Nat.sub(R.length(ts), len), b2, m) : Nat}) -> {R.next.mode(all, last, len, ts, R.Policy{s, b1, m}) == R.next.mode(all, last, len, ts, R.Policy{s, b2, m}) : Maybe<&2, R.Switch>}:
  match all:
    case True{}:
      %e : {R.pick.back(R.order(last, len), ts, R.double(Nat.sub(R.length(ts), len), b1, m), m) == R.pick.back(R.order(last, len), ts, _, m) : Maybe<&2, R.Switch>}
      {==}
    case False{}:
      {==}

def rx.bs_budget(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +s: Nat, +b1: Nat, +b2: Nat, +m: Nat, e: {R.double(Nat.sub(R.length(ts), len), b1, m) == R.double(Nat.sub(R.length(ts), len), b2, m) : Nat}) -> {R.next.budget(ok, last, len, ts, R.Policy{s, b1, m}) == R.next.budget(ok, last, len, ts, R.Policy{s, b2, m}) : Maybe<&2, R.Switch>}:
  match ok:
    case True{}:
      rx.bs_mode(R.all_seen(len, ts), last, len, ts, s, b1, b2, m, e)
    case False{}:
      {==}

def base_saturation_walk(+len: Nat, ts: List<&2, R.Tried>, +s: Nat, +b: Nat, +m: Nat, +c: Nat, +h: {Nat.is_le(m, c) == True{} : Bool}) -> {R.next(len, ts, R.Policy{s, Nat.min(b, c), m}) == R.next(len, ts, R.Policy{s, b, m}) : Maybe<&2, R.Switch>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      +k = Nat.sub(R.length(t <> rest), len)
      +e = Equal.trans(Nat, R.double(k, Nat.min(b, c), m), Nat.min(Retry.rs.twice(k, Nat.min(b, c)), m), R.double(k, b, m), LA.rx.double(k, Nat.min(b, c), m), Equal.trans(Nat, Nat.min(Retry.rs.twice(k, Nat.min(b, c)), m), Nat.min(Retry.rs.twice(k, b), m), R.double(k, b, m), rx.base_sat(Nat.is_le(b, c), k, b, m, c, {==}, h), Equal.sym(Nat, R.double(k, b, m), Nat.min(Retry.rs.twice(k, b), m), LA.rx.double(k, b, m))))
      rx.bs_budget(Nat.is_le(R.length(t <> rest), s), R.Tried.at(R.last.go(rest, t)), len, t <> rest, s, Nat.min(b, c), b, m, e)

def Retry.failover_base_saturation_exact(len, ts, switches, base, max, c, at_least):
  base_saturation_walk(len, ts, switches, base, max, c, at_least)
