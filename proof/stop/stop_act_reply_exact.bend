# eukhe: the proof of LAW stop_act_reply_exact
#
# PROOF: act by act, both sides compute, whatever the reply as it was.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/stop.bend as Stop

def stp.act_reply(a: RnRecovery.Act, pass: RnState.Reply) -> {RnRecovery.Act.reply(a, pass) == Stop.spec_act_reply(a, pass) : RnState.Reply}:
  match a:
    case RnRecovery.Pass{}:
      {==}
    case RnRecovery.Exec{}:
      {==}
    case RnRecovery.Redo{}:
      {==}
    case RnRecovery.Quit{}:
      {==}
    case RnRecovery.Shrink{}:
      {==}
    case RnRecovery.Lower{}:
      {==}

def Stop.stop_act_reply_exact(a, pass):
  stp.act_reply(a, pass)
