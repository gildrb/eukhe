# eukhe: the proof of LAW rec_redo_retries_with_a_note
#
# PROOF: a Redo's reply is a noted error that is not retryable (by computation), and a noted reply notes while the notes last (LA.rk.note_budget).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover
import ./base.bend as LA

def RunRecover.rec_redo_retries_with_a_note(pass, l, t):
  LA.rk.note_budget(l, t, False{})
