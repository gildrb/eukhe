# eukhe: the proof of LAW undo_turn_takes
#
# PROOF: by cases on the state: the model answers a turn start Took on both
# fields as they are.

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def Undo.undo_turn_takes(st, t):
  match st:
    case U.St{l, m}:
      {==}
