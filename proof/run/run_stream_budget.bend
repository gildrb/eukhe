# eukhe: the proof of LAW run_stream_budget
#
# PROOF: the reply's step under the flag is the rule through on_stream
# (LA.rk.stream_rule); the budget match spends while the budget lasts and
# passes its spent-out step otherwise (stream.spend), and the spent-out
# side carries the no-flag rule's step (LA.rk.reply_rule).

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

# on_stream spends while the budget lasts, else passes its spent-out step
def stream.spend(+spent_out: RnDecision.Then, +left: Nat, +spent: Nat) -> {RnDecision.Then.on_stream(spent_out, True{}, left, spent) == Run.then_if(Nat.is_lt(spent, left), RnDecision.DoRetry{}, spent_out) : RnDecision.Then}:
  match left spent:
    case 0n 0n:
      {==}
    case 0n 1n+x:
      {==}
    case 1n+m 0n:
      {==}
    case 1n+m 1n+x:
      stream.spend(spent_out, m, x)

# the else-branch of then_if carries the step it wraps
def stream.else_cong(+b: Bool, +x: RnDecision.Then, +y1: RnDecision.Then, +y2: RnDecision.Then, +e: {y1 == y2 : RnDecision.Then}) -> {Run.then_if(b, x, y1) == Run.then_if(b, x, y2) : RnDecision.Then}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def Run.run_stream_budget(l, i, j, k, w, c):
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most, +streams}:
      +lim = {RnDecision.Lim{rounds, wait, retries, most, streams} : RnDecision.Lim}
      +at = {RnDecision.At{1n+Nat.add(Nat.add(j, i), k), j, k, w, c} : RnDecision.At}
      +cut = LA.rk.r_reply(lim, at, RnState.Error{True{}, False{}})
      +flagged = {RnDecision.decide.reply(lim, at, RnState.Error{True{}, False{}}, True{}) : RnDecision.Then}
      +plain = {RnDecision.decide.reply(lim, at, RnState.Error{True{}, False{}}, False{}) : RnDecision.Then}
      +goal = {Run.then_if(Nat.is_lt(k, streams), RnDecision.DoRetry{}, plain) : RnDecision.Then}
      Equal.trans(
        RnDecision.Then,
        flagged,
        Run.then_if(Nat.is_lt(k, streams), RnDecision.DoRetry{}, cut),
        goal,
        Equal.trans(
          RnDecision.Then,
          flagged,
          RnDecision.Then.on_stream(cut, True{}, streams, k),
          Run.then_if(Nat.is_lt(k, streams), RnDecision.DoRetry{}, cut),
          LA.rk.stream_rule(lim, at, RnState.Error{True{}, False{}}, True{}),
          stream.spend(cut, streams, k)),
        stream.else_cong(Nat.is_lt(k, streams), RnDecision.DoRetry{}, cut, plain, LA.rk.reply_rule(lim, at, RnState.Error{True{}, False{}})))
