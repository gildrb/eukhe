# eukhe: the proof of LAW failover_return_backoff
# A switch to a provider the request tried is no fresh pick (whose
# provider was not tried), so it is the return pick (LW.fw.split): its wait
# is the longer of the model's backoff and the provider's server's wait
# (LW.fw.back_of), which is R3's return wait (LW.fw.return_wait).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ../base/retry.bend as LRetry
import ./base/walk.bend as LW

def rb.mode(all: Bool, +len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, M: LW.fw.Mode(all, len, ts, last, R.Policy{sw, b, m}, to, w), tried: {Retry.rs.tried(to, ts) == True{} : Bool}) -> {w == Retry.rs.return_wait(to, len, ts, b, m) : Nat}:
  match all:
    case True{}:
      (ea, pb) = M
      +B = R.backoff(R.Policy{sw, b, m}, len, ts)
      +S = R.server(to, ts)
      +K = LW.fw.back_of(ts, to, w, R.order(last, len), last, B, m, LRetry.rp.order_notin(last, len), pb)
      +k1 = LLogicBool.rp.and_l(Nat.is_eq(Nat.max(B, S), w), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, m))), K)
      Equal.trans(Nat, w, Nat.max(B, S), Retry.rs.return_wait(to, len, ts, b, m), Equal.sym(Nat, Nat.max(B, S), w, LLogicNat.rp.eq_true(Nat.max(B, S), w, k1)), LW.fw.return_wait(to, sw, b, m, len, ts))
    case False{}:
      (ea, pf) = M
      +F = LW.fw.fresh_of(ts, to, w, R.order(last, len), last, LRetry.rp.order_notin(last, len), pf)
      +ns = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), LLogicBool.rp.and_r(Nat.is_eq(w, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))), F))
      +sf = LW.fw.not_t(R.seen(to, ts), ns)
      LLogicLogic.rp.absurdT({w == Retry.rs.return_wait(to, len, ts, b, m) : Nat}, Equal.trans(Bool, True{}, Retry.rs.tried(to, ts), False{}, Equal.sym(Bool, Retry.rs.tried(to, ts), True{}, tried), Equal.trans(Bool, Retry.rs.tried(to, ts), R.seen(to, ts), False{}, Equal.sym(Bool, R.seen(to, ts), Retry.rs.tried(to, ts), LW.fw.tried(to, ts)), sf)))

def rb.split(+len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, sp: LW.fw.Split(len, ts, last, R.Policy{sw, b, m}, to, w), tried: {Retry.rs.tried(to, ts) == True{} : Bool}) -> {w == Retry.rs.return_wait(to, len, ts, b, m) : Nat}:
  (B, S) = sp
  (all, M) = S
  rb.mode(all, len, ts, last, sw, b, m, to, w, M, tried)

def return_backoff(+len: Nat, ts: List<&2, R.Tried>, +sw: Nat, +b: Nat, +m: Nat, +to: Nat, +w: Nat, got: {R.next(len, ts, R.Policy{sw, b, m}) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}, tried: {Retry.rs.tried(to, ts) == True{} : Bool}) -> {w == Retry.rs.return_wait(to, len, ts, b, m) : Nat}:
  match ts:
    case Nil{}:
      LW.fw.none_some({w == Retry.rs.return_wait(to, len, Nil{}, b, m) : Nat}, R.Switch{to, w}, got)
    case +t <> +rest:
      rb.split(len, t <> rest, R.Tried.at(R.last.go(rest, t)), sw, b, m, to, w, LW.fw.split(len, t, rest, R.Policy{sw, b, m}, to, w, got), tried)

def Retry.failover_return_backoff(len, ts, switches, base, max, to, w, got, tried):
  return_backoff(len, ts, switches, base, max, to, w, got, tried)
