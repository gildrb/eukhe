# eukhe: the proof of LAW failover_return_waits
# A switch to a provider the request tried is no fresh pick (whose
# provider was not tried), so it is the return pick (LW.fw.split): its wait
# is positive, and it is the longer of the backoff and the provider's
# server's wait (LW.fw.back_of), which is the laws' rs.wait (LW.fw.wait).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ../base/nat.bend as LNat
import ../base/retry.bend as LRetry
import ./base/walk.bend as LW

def rwt.mode(all: Bool, +len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, +to: Nat, +w: Nat, M: LW.fw.Mode(all, len, ts, last, p, to, w), tried: {Retry.rs.tried(to, ts) == True{} : Bool}) -> {Nat.is_gt(w, 0n) == True{} : Bool} & {Nat.is_ge(w, Retry.rs.wait(to, ts, 0n)) == True{} : Bool}:
  match all:
    case True{}:
      (ea, pb) = M
      +B = R.backoff(p, len, ts)
      +X = R.Policy.max(p)
      +S = R.server(to, ts)
      +K = LW.fw.back_of(ts, to, w, R.order(last, len), last, B, X, LRetry.rp.order_notin(last, len), pb)
      +k1 = LLogicBool.rp.and_l(Nat.is_eq(Nat.max(B, S), w), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, X))), K)
      +k2 = LLogicBool.rp.and_r(Nat.is_eq(Nat.max(B, S), w), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, X))), K)
      +k3 = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, X)), k2)
      +gt = LLogicBool.rp.and_l(Nat.is_gt(w, 0n), Nat.is_le(w, X), k3)
      +ge = LNat.rp.ge_move(Nat.max(B, S), w, S, LLogicNat.rp.eq_true(Nat.max(B, S), w, k1), Nat.max_ge_r(B, S))
      (gt, Equal.trans(Bool, Nat.is_ge(w, Retry.rs.wait(to, ts, 0n)), Nat.is_ge(w, S), True{}, Equal.cong(Nat, Bool, z => Nat.is_ge(w, z), Retry.rs.wait(to, ts, 0n), S, Equal.sym(Nat, S, Retry.rs.wait(to, ts, 0n), LW.fw.wait(to, ts, 0n))), ge))
    case False{}:
      (ea, pf) = M
      +F = LW.fw.fresh_of(ts, to, w, R.order(last, len), last, LRetry.rp.order_notin(last, len), pf)
      +ns = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), LLogicBool.rp.and_r(Nat.is_eq(w, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))), F))
      +sf = LW.fw.not_t(R.seen(to, ts), ns)
      LLogicLogic.rp.absurdT({Nat.is_gt(w, 0n) == True{} : Bool} & {Nat.is_ge(w, Retry.rs.wait(to, ts, 0n)) == True{} : Bool}, Equal.trans(Bool, True{}, Retry.rs.tried(to, ts), False{}, Equal.sym(Bool, Retry.rs.tried(to, ts), True{}, tried), Equal.trans(Bool, Retry.rs.tried(to, ts), R.seen(to, ts), False{}, Equal.sym(Bool, R.seen(to, ts), Retry.rs.tried(to, ts), LW.fw.tried(to, ts)), sf)))

def rwt.split(+len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, +to: Nat, +w: Nat, sp: LW.fw.Split(len, ts, last, p, to, w), tried: {Retry.rs.tried(to, ts) == True{} : Bool}) -> {Nat.is_gt(w, 0n) == True{} : Bool} & {Nat.is_ge(w, Retry.rs.wait(to, ts, 0n)) == True{} : Bool}:
  (B, S) = sp
  (all, M) = S
  rwt.mode(all, len, ts, last, p, to, w, M, tried)

def return_waits(+len: Nat, ts: List<&2, R.Tried>, +p: R.Policy, +to: Nat, +w: Nat, got: {R.next(len, ts, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}, tried: {Retry.rs.tried(to, ts) == True{} : Bool}) -> {Nat.is_gt(w, 0n) == True{} : Bool} & {Nat.is_ge(w, Retry.rs.wait(to, ts, 0n)) == True{} : Bool}:
  match ts:
    case Nil{}:
      LW.fw.none_some({Nat.is_gt(w, 0n) == True{} : Bool} & {Nat.is_ge(w, Retry.rs.wait(to, Nil{}, 0n)) == True{} : Bool}, R.Switch{to, w}, got)
    case +t <> +rest:
      rwt.split(len, t <> rest, R.Tried.at(R.last.go(rest, t)), p, to, w, LW.fw.split(len, t, rest, p, to, w, got), tried)

def Retry.failover_return_waits(len, ts, p, to, w, got, tried):
  return_waits(len, ts, p, to, w, got, tried)
