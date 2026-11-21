# eukhe: the proof of LAW undo_state
#
# PROOF: the state after the history is the backward count of undos and the oldest turn (LA.unb.state: one event at a time, the count with k undos to go dropping k turns, LA.unb.live_drop).

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def Undo.undo_state(h):
  LA.unb.state(h)
