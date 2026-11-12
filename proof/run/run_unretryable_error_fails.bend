# eukhe: the proof of LAW run_unretryable_error_fails
#
# PROOF: the reply's step is the rule over the grown counts (LA.rk.reply_rule); an error the policy cannot cure is no retry.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def Run.run_unretryable_error_fails(l, t):
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          LA.rk.reply_rule(RnDecision.Lim{rounds, wait, retries, most}, RnDecision.At{attempt, notes, waited, compacted}, RnState.Error{False{}, False{}})
