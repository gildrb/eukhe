# eukhe: the proof of LAW run_retry_budget
#
# PROOF: the reply's step is the rule over the grown counts (LA.rk.reply_rule); the retries spent, (1 + j + i - 1) - j, are i.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def retry.spent(+i: Nat, +j: Nat, +retries: Nat) -> {LA.rk.r_retry(Nat.is_lt(Nat.sub(Nat.sub(1n+Nat.add(j, i), 1n), j), retries)) == Run.then_if(Nat.is_lt(i, retries), RnDecision.DoRetry{}, RnDecision.DoFail{}) : RnDecision.Then}:
  %LA.rk.sub0(Nat.add(j, i)) : {LA.rk.r_retry(Nat.is_lt(Nat.sub(_, j), retries)) == Run.then_if(Nat.is_lt(i, retries), RnDecision.DoRetry{}, RnDecision.DoFail{}) : RnDecision.Then}
  %LA.rk.addsub(j, i) : {LA.rk.r_retry(Nat.is_lt(_, retries)) == Run.then_if(Nat.is_lt(i, retries), RnDecision.DoRetry{}, RnDecision.DoFail{}) : RnDecision.Then}
  LA.rk.retry_if(Nat.is_lt(i, retries))

def Run.run_retry_budget(l, i, j, w, c):
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      +lim = {RnDecision.Lim{rounds, wait, retries, most} : RnDecision.Lim}
      +at = {RnDecision.At{1n+Nat.add(j, i), j, w, c} : RnDecision.At}
      +goal = {Run.then_if(Nat.is_lt(i, retries), RnDecision.DoRetry{}, RnDecision.DoFail{}) : RnDecision.Then}
      Equal.trans(RnDecision.Then, RnDecision.decide.reply(lim, at, RnState.Error{True{}, False{}}), LA.rk.r_reply(lim, at, RnState.Error{True{}, False{}}), goal, LA.rk.reply_rule(lim, at, RnState.Error{True{}, False{}}), retry.spent(i, j, retries))
