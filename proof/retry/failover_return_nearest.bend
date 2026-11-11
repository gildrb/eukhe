# eukhe: the proof of LAW failover_return_nearest
# A switch to a provider the request tried is no fresh pick (whose
# provider was not tried), so it is the return pick (LW.fw.split) over the
# chain order after the provider that just failed; that order ranks each
# of its providers at its rs.rank (LW.fw.order_ranked) and holds x
# (LW.fw.order_mem); a return to x may go out by the model's test exactly
# when R3's (LW.fw.return_wait); the return pick is no later than any
# provider of it a return may go to (LW.fw.back_nearest).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/retry.bend as LRetry
import ./base/walk.bend as LW

def rn.mode(all: Bool, +len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, +x: Nat, M: LW.fw.Mode(all, len, ts, last, R.Policy{sw, b, m}, to, w), st: {R.seen(to, ts) == True{} : Bool}, chain: {Nat.is_lt(x, len) == True{} : Bool}, other: {Nat.is_eq(x, last) == False{} : Bool}, ok: {LW.fw.ok(x, ts, R.backoff(R.Policy{sw, b, m}, len, ts), m) == True{} : Bool}) -> {Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, x, len)) == True{} : Bool}:
  match all:
    case True{}:
      (ea, pb) = M
      +ord = R.order(last, len)
      +B = R.backoff(R.Policy{sw, b, m}, len, ts)
      LW.fw.back_nearest(ord, LW.fw.hd(ord, x), LW.fw.hb(ord, ts, B, m), 0n, last, len, ts, B, m, to, w, x, {==}, {==}, LW.fw.order_ranked(last, len), pb, LW.fw.order_mem(last, len, x, chain, other), ok)
    case False{}:
      (ea, pf) = M
      +F = LW.fw.fresh_of(ts, to, w, R.order(last, len), last, LRetry.rp.order_notin(last, len), pf)
      +ns = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), LLogicBool.rp.and_r(Nat.is_eq(w, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))), F))
      LLogicLogic.rp.absurdT({Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, x, len)) == True{} : Bool}, Equal.trans(Bool, True{}, R.seen(to, ts), False{}, Equal.sym(Bool, R.seen(to, ts), True{}, st), LW.fw.not_t(R.seen(to, ts), ns)))

def rn.split(+len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, +x: Nat, sp: LW.fw.Split(len, ts, last, R.Policy{sw, b, m}, to, w), st: {R.seen(to, ts) == True{} : Bool}, chain: {Nat.is_lt(x, len) == True{} : Bool}, other: {Nat.is_eq(x, last) == False{} : Bool}, ok: {LW.fw.ok(x, ts, R.backoff(R.Policy{sw, b, m}, len, ts), m) == True{} : Bool}) -> {Nat.is_le(Retry.rs.rank(last, to, len), Retry.rs.rank(last, x, len)) == True{} : Bool}:
  (B, S) = sp
  (all, M) = S
  rn.mode(all, len, ts, last, sw, b, m, to, w, x, M, st, chain, other, ok)

def return_nearest(+len: Nat, +t: R.Tried, +rest: List<&2, R.Tried>, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, +x: Nat, got: {R.next(len, t <> rest, R.Policy{sw, b, m}) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}, tried: {Retry.rs.tried(to, t <> rest) == True{} : Bool}, chain: {Nat.is_lt(x, len) == True{} : Bool}, other: {Nat.is_eq(x, Retry.rs.newest(rest, t)) == False{} : Bool}, may: {Retry.rs.may_return(x, len, t <> rest, b, m) == True{} : Bool}) -> {Nat.is_le(Retry.rs.rank(Retry.rs.newest(rest, t), to, len), Retry.rs.rank(Retry.rs.newest(rest, t), x, len)) == True{} : Bool}:
  +L = {t <> rest : List<&2, R.Tried>}
  +last = R.Tried.at(R.last.go(rest, t))
  +B = R.backoff(R.Policy{sw, b, m}, len, L)
  %LW.fw.newest(rest, t) : {Nat.is_le(Retry.rs.rank(_, to, len), Retry.rs.rank(_, x, len)) == True{} : Bool}
  +st = Equal.trans(Bool, R.seen(to, L), Retry.rs.tried(to, L), True{}, LW.fw.tried(to, L), tried)
  +ot = Equal.trans(Bool, Nat.is_eq(x, last), Nat.is_eq(x, Retry.rs.newest(rest, t)), False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(x, z), last, Retry.rs.newest(rest, t), LW.fw.newest(rest, t)), other)
  +ok = Equal.trans(Bool, LW.fw.ok(x, L, B, m), Retry.rs.may_return(x, len, L, b, m), True{}, Equal.cong(Nat, Bool, z => Bool.and(Nat.is_gt(z, 0n), Nat.is_le(z, m)), Nat.max(B, R.server(x, L)), Retry.rs.return_wait(x, len, L, b, m), LW.fw.return_wait(x, sw, b, m, len, L)), may)
  rn.split(len, L, last, sw, b, m, to, w, x, LW.fw.split(len, t, rest, R.Policy{sw, b, m}, to, w, got), st, chain, ot, ok)

def Retry.failover_return_nearest(len, t, rest, switches, base, max, to, w, x, got, tried, chain, other, may):
  return_nearest(len, t, rest, switches, base, max, to, w, x, got, tried, chain, other, may)
