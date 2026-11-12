# eukhe: the proof of LAW run_message_reply
#
# PROOF: a message with a call is the calls and one with text is the answer (by computation); one with neither is a noted error (LA.rk.note_budget).

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def Run.run_message_reply(text, l, t):
  ({==}, {==}, LA.rk.note_budget(l, t, False{}))
