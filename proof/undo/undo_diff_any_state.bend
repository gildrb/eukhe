# eukhe: the proof of LAW undo_diff_any_state
#
# PROOF: by cases on the free fields: each state and event is then made of
# constructors, so each /diff reduces to its answer.

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def Undo.undo_diff_any_state(t, rest, live, b, f):
  match live:
    case Nil{}:
      match b:
        case None{}:
          ({==}, {==}, {==}, {==})
        case Some{y}:
          ({==}, {==}, {==}, {==})
    case Con{x, xs}:
      match b:
        case None{}:
          ({==}, {==}, {==}, {==})
        case Some{y}:
          ({==}, {==}, {==}, {==})
