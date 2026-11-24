# eukhe: the proof of LAW run_overflow_compacts_once
#
# PROOF: the reply's step is the rule over the grown counts (LA.rk.reply_rule): an overflow compacts when it has a cut and the generation has not compacted.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def over.no_cut(+lim: RnDecision.Lim, +t: RnDecision.At) -> {RnDecision.decide.reply(lim, t, RnState.Overflow{False{}}, False{}) == RnDecision.DoFail{} : RnDecision.Then}:
  match lim:
    case RnDecision.Lim{+rounds, +wait, +retries, +most, +streams}:
      match t:
        case RnDecision.At{+attempt, +notes, +spent, +waited, +compacted}:
          LA.rk.reply_rule(RnDecision.Lim{rounds, wait, retries, most, streams}, RnDecision.At{attempt, notes, spent, waited, compacted}, RnState.Overflow{False{}})

def Run.run_overflow_compacts_once(l, a, j, k, w, t):
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most, +streams}:
      +lim = {RnDecision.Lim{rounds, wait, retries, most, streams} : RnDecision.Lim}
      (LA.rk.reply_rule(lim, RnDecision.At{a, j, k, w, False{}}, RnState.Overflow{True{}}), LA.rk.reply_rule(lim, RnDecision.At{a, j, k, w, True{}}, RnState.Overflow{True{}}), over.no_cut(lim, t))
