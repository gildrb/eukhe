# eukhe: the proof of LAW run_reply_answers_or_runs_tools
#
# PROOF: a text reply answers and calls go to the tools phase, whatever the counts (by computation).

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def Run.run_reply_answers_or_runs_tools(l, t):
  ({==}, {==})
