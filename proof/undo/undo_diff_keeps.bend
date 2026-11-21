# eukhe: the proof of LAW undo_diff_keeps
#
# PROOF: by cases on the state and the scope: the model keeps both fields.

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def Undo.undo_diff_keeps(st, s):
  match st:
    case U.St{l, m}:
      match s:
        case U.Turn{}:
          {==}
        case U.All{}:
          {==}
