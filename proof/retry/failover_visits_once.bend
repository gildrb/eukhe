# eukhe: the proof of LAW failover_visits_once
# A switch is the fresh pick, whose provider was not tried, or the return
# pick, made only once every provider of the chain was tried
# (LW.fw.split, LW.fw.all_seen).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/retry.bend as LRetry
import ./base/walk.bend as LW

def vo.mode(all: Bool, +len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, +to: Nat, +w: Nat, M: LW.fw.Mode(all, len, ts, last, p, to, w), tried: {Retry.rs.tried(to, ts) == True{} : Bool}) -> {Retry.rs.all_tried(Retry.rs.ints(len, 0n), ts) == True{} : Bool}:
  match all:
    case True{}:
      (ea, pb) = M
      Equal.trans(Bool, Retry.rs.all_tried(Retry.rs.ints(len, 0n), ts), R.all_seen(len, ts), True{}, Equal.sym(Bool, R.all_seen(len, ts), Retry.rs.all_tried(Retry.rs.ints(len, 0n), ts), LW.fw.all_seen(len, ts)), ea)
    case False{}:
      (ea, pf) = M
      +F = LW.fw.fresh_of(ts, to, w, R.order(last, len), last, LRetry.rp.order_notin(last, len), pf)
      +ns = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), LLogicBool.rp.and_r(Nat.is_eq(w, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))), F))
      +sf = LW.fw.not_t(R.seen(to, ts), ns)
      LLogicLogic.rp.absurdT({Retry.rs.all_tried(Retry.rs.ints(len, 0n), ts) == True{} : Bool}, Equal.trans(Bool, True{}, Retry.rs.tried(to, ts), False{}, Equal.sym(Bool, Retry.rs.tried(to, ts), True{}, tried), Equal.trans(Bool, Retry.rs.tried(to, ts), R.seen(to, ts), False{}, Equal.sym(Bool, R.seen(to, ts), Retry.rs.tried(to, ts), LW.fw.tried(to, ts)), sf)))

def vo.split(+len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, +to: Nat, +w: Nat, sp: LW.fw.Split(len, ts, last, p, to, w), tried: {Retry.rs.tried(to, ts) == True{} : Bool}) -> {Retry.rs.all_tried(Retry.rs.ints(len, 0n), ts) == True{} : Bool}:
  (B, S) = sp
  (all, M) = S
  vo.mode(all, len, ts, last, p, to, w, M, tried)

def visits_once(+len: Nat, ts: List<&2, R.Tried>, +p: R.Policy, +to: Nat, +w: Nat, got: {R.next(len, ts, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}, tried: {Retry.rs.tried(to, ts) == True{} : Bool}) -> {Retry.rs.all_tried(Retry.rs.ints(len, 0n), ts) == True{} : Bool}:
  match ts:
    case Nil{}:
      LW.fw.none_some({Retry.rs.all_tried(Retry.rs.ints(len, 0n), Nil{}) == True{} : Bool}, R.Switch{to, w}, got)
    case +t <> +rest:
      vo.split(len, t <> rest, R.Tried.at(R.last.go(rest, t)), p, to, w, LW.fw.split(len, t, rest, p, to, w, got), tried)

def Retry.failover_visits_once(len, ts, p, to, w, got, tried):
  visits_once(len, ts, p, to, w, got, tried)
