# eukhe: the proof of LAW failover_never_twice_in_a_row
# A switch is the fresh or the return pick over the chain order after the
# provider that just failed (LW.fw.split), which never holds it
# (LRetry.rp.order_notin): each pick's switch is to another provider. The
# provider that just failed is the laws' newest attempt's (LW.fw.newest).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/bool.bend as LLogicBool
import ../base/retry.bend as LRetry
import ./base/walk.bend as LW

def nt.mode(all: Bool, +len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, +to: Nat, +w: Nat, M: LW.fw.Mode(all, len, ts, last, p, to, w)) -> {Nat.is_eq(to, last) == False{} : Bool}:
  match all:
    case True{}:
      (ea, pb) = M
      +B = R.backoff(p, len, ts)
      +X = R.Policy.max(p)
      +K = LW.fw.back_of(ts, to, w, R.order(last, len), last, B, X, LRetry.rp.order_notin(last, len), pb)
      +k2 = LLogicBool.rp.and_r(Nat.is_eq(Nat.max(B, R.server(to, ts)), w), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, X))), K)
      LW.fw.not_t(Nat.is_eq(to, last), LLogicBool.rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, X)), k2))
    case False{}:
      (ea, pf) = M
      +F = LW.fw.fresh_of(ts, to, w, R.order(last, len), last, LRetry.rp.order_notin(last, len), pf)
      +f2 = LLogicBool.rp.and_r(Nat.is_eq(w, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))), F)
      LW.fw.not_t(Nat.is_eq(to, last), LLogicBool.rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), f2))

def nt.split(+len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, +to: Nat, +w: Nat, sp: LW.fw.Split(len, ts, last, p, to, w)) -> {Nat.is_eq(to, last) == False{} : Bool}:
  (B, S) = sp
  (all, M) = S
  nt.mode(all, len, ts, last, p, to, w, M)

def never_twice(+len: Nat, +t: R.Tried, +rest: List<&2, R.Tried>, +p: R.Policy, +to: Nat, +w: Nat, got: {R.next(len, t <> rest, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}) -> {Nat.is_eq(to, Retry.rs.newest(rest, t)) == False{} : Bool}:
  %LW.fw.newest(rest, t) : {Nat.is_eq(to, _) == False{} : Bool}
  nt.split(len, t <> rest, R.Tried.at(R.last.go(rest, t)), p, to, w, LW.fw.split(len, t, rest, p, to, w, got))

def Retry.failover_never_twice_in_a_row(len, t, rest, p, to, w, got):
  never_twice(len, t, rest, p, to, w, got)
