# eukhe: the proof of LAW run_deferred_polls_until_deadline
#
# PROOF: the reply's step is the rule over the grown counts (LA.rk.reply_rule): a poll while waited < wait, else the deadline.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def Run.run_deferred_polls_until_deadline(l, t):
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          Equal.trans(RnDecision.Then, RnDecision.decide.reply(RnDecision.Lim{rounds, wait, retries, most}, RnDecision.At{attempt, notes, waited, compacted}, RnState.Deferred{}), LA.rk.r_reply(RnDecision.Lim{rounds, wait, retries, most}, RnDecision.At{attempt, notes, waited, compacted}, RnState.Deferred{}), Run.then_if(Nat.is_lt(waited, wait), RnDecision.DoPoll{}, RnDecision.DoLate{}), LA.rk.reply_rule(RnDecision.Lim{rounds, wait, retries, most}, RnDecision.At{attempt, notes, waited, compacted}, RnState.Deferred{}), LA.rk.wait_if(Nat.is_lt(waited, wait)))
