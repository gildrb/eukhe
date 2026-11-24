# eukhe: the proof of LAW run_unretryable_error_fails
#
# PROOF: the reply's step is the rule over the grown counts (LA.rk.reply_rule).

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def Run.run_unretryable_error_fails(l, t):
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most, +streams}:
      match t:
        case RnDecision.At{+attempt, +notes, +spent, +waited, +compacted}:
          LA.rk.reply_rule(RnDecision.Lim{rounds, wait, retries, most, streams}, RnDecision.At{attempt, notes, spent, waited, compacted}, RnState.Error{False{}, False{}})
