# eukhe: the proof of LAW rec_redo_is_noted

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../laws/run.bend as Run

def redo_is_noted(-pass: RnState.Reply) -> {RnRecovery.Act.reply(RnRecovery.Redo{}, pass) == RnState.Error{False{}, True{}} : RnState.Reply}:
  {==}

def Run.rec_redo_is_noted(pass):
  redo_is_noted(pass)
