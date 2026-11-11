# eukhe: the proof of LAW run_note_budget
#
# PROOF: the reply's step is the rule over the grown counts (LA.rk.reply_rule): a note while notes < MAX_NOTES (LA.rk.note_budget).

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def Run.run_note_budget(l, t, retryable):
  LA.rk.note_budget(l, t, retryable)
