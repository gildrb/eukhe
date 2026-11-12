# eukhe: the proof of LAW failover_delay_capped
# A switch is the fresh pick, which waits 0, or the return pick, which
# waits at most max (LW.fw.split, LW.fw.fresh_of, LW.fw.back_of).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/nat.bend as LLogicNat
import ../base/nat.bend as LNat
import ../base/retry.bend as LRetry
import ./base/walk.bend as LW
import ../base/logic/logic.bend as LLogicLogic

def dc.mode(all: Bool, +len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, M: LW.fw.Mode(all, len, ts, last, R.Policy{sw, b, m}, to, w)) -> {Nat.is_le(w, m) == True{} : Bool}:
  match all:
    case True{}:
      (ea, pb) = M
      +B = R.backoff(R.Policy{sw, b, m}, len, ts)
      +K = LW.fw.back_of(ts, to, w, R.order(last, len), last, B, m, LRetry.rp.order_notin(last, len), pb)
      +k2 = LLogicBool.rp.and_r(Nat.is_eq(Nat.max(B, R.server(to, ts)), w), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, m))), K)
      +k3 = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, m)), k2)
      LLogicBool.rp.and_r(Nat.is_gt(w, 0n), Nat.is_le(w, m), k3)
    case False{}:
      (ea, pf) = M
      +F = LW.fw.fresh_of(ts, to, w, R.order(last, len), last, LRetry.rp.order_notin(last, len), pf)
      +w0 = LLogicNat.rp.eq_true(w, 0n, LLogicBool.rp.and_l(Nat.is_eq(w, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))), F))
      %Equal.sym(Nat, w, 0n, w0) : {Nat.is_le(_, m) == True{} : Bool}
      LNat.rp.le_zero(m)

def dc.split(+len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, sp: LW.fw.Split(len, ts, last, R.Policy{sw, b, m}, to, w)) -> {Nat.is_le(w, m) == True{} : Bool}:
  (B, S) = sp
  (all, M) = S
  dc.mode(all, len, ts, last, sw, b, m, to, w, M)

def delay_capped(+len: Nat, ts: List<&2, R.Tried>, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, got: {R.next(len, ts, R.Policy{sw, b, m}) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}) -> {Nat.is_le(w, m) == True{} : Bool}:
  match ts:
    case Nil{}:
      LW.fw.none_some({Nat.is_le(w, m) == True{} : Bool}, R.Switch{to, w}, got)
    case +t <> +rest:
      dc.split(len, t <> rest, R.Tried.at(R.last.go(rest, t)), sw, b, m, to, w, LW.fw.split(len, t, rest, R.Policy{sw, b, m}, to, w, got))

def Retry.failover_delay_capped(len, ts, switches, base, max, to, w, got):
  delay_capped(len, ts, switches, base, max, to, w, got)
