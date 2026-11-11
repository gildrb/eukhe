# eukhe: the proof of LAW failover_in_chain
# A switch is a pick over the chain order after the provider that just
# failed (LW.fw.split), whose providers are all below len
# (LW.fw.order_below); a pick goes to one of them (LW.fw.fresh_lt,
# LW.fw.back_lt).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./base/walk.bend as LW

def ic.mode(all: Bool, +len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, -to: Nat, -w: Nat, M: LW.fw.Mode(all, len, ts, last, p, to, w)) -> {Nat.is_lt(to, len) == True{} : Bool}:
  match all:
    case True{}:
      (ea, pb) = M
      +B = R.backoff(p, len, ts)
      +X = R.Policy.max(p)
      Equal.trans(Bool, LW.fw.pick_lt(Some{R.Switch{to, w}}, len), LW.fw.pick_lt(R.pick.back(R.order(last, len), ts, B, X), len), True{}, Equal.cong(Maybe<&2, R.Switch>, Bool, k => LW.fw.pick_lt(k, len), Some{R.Switch{to, w}}, R.pick.back(R.order(last, len), ts, B, X), Equal.sym(Maybe<&2, R.Switch>, R.pick.back(R.order(last, len), ts, B, X), Some{R.Switch{to, w}}, pb)), LW.fw.back_lt(R.order(last, len), ts, B, X, len, LW.fw.order_below(last, len)))
    case False{}:
      (ea, pf) = M
      Equal.trans(Bool, LW.fw.pick_lt(Some{R.Switch{to, w}}, len), LW.fw.pick_lt(R.pick.fresh(R.order(last, len), ts), len), True{}, Equal.cong(Maybe<&2, R.Switch>, Bool, k => LW.fw.pick_lt(k, len), Some{R.Switch{to, w}}, R.pick.fresh(R.order(last, len), ts), Equal.sym(Maybe<&2, R.Switch>, R.pick.fresh(R.order(last, len), ts), Some{R.Switch{to, w}}, pf)), LW.fw.fresh_lt(R.order(last, len), ts, len, LW.fw.order_below(last, len)))

def ic.split(+len: Nat, +ts: List<&2, R.Tried>, +last: Nat, +p: R.Policy, -to: Nat, -w: Nat, sp: LW.fw.Split(len, ts, last, p, to, w)) -> {Nat.is_lt(to, len) == True{} : Bool}:
  (B, S) = sp
  (all, M) = S
  ic.mode(all, len, ts, last, p, to, w, M)

def in_chain(+len: Nat, ts: List<&2, R.Tried>, +p: R.Policy, +to: Nat, +w: Nat, got: {R.next(len, ts, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}) -> {Nat.is_lt(to, len) == True{} : Bool}:
  match ts:
    case Nil{}:
      LW.fw.none_some({Nat.is_lt(to, len) == True{} : Bool}, R.Switch{to, w}, got)
    case +t <> +rest:
      ic.split(len, t <> rest, R.Tried.at(R.last.go(rest, t)), p, to, w, LW.fw.split(len, t, rest, p, to, w, got))

def Retry.failover_in_chain(len, ts, p, to, w, got):
  in_chain(len, ts, p, to, w, got)
