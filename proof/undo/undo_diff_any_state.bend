# eukhe: the proof of LAW undo_diff_any_state
#
# PROOF: by cases on the turns and the first snapshot: the state and the
# event are then constructors, so each /diff reduces to its comparison.

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def Undo.undo_diff_any_state(live, b):
  match live:
    case Nil{}:
      match b:
        case None{}:
          ({==}, {==})
        case Some{x}:
          ({==}, {==})
    case Con{t, rest}:
      match b:
        case None{}:
          ({==}, {==})
        case Some{x}:
          ({==}, {==})
