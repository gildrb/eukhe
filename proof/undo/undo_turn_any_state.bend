# eukhe: the proof of LAW undo_turn_any_state
#
# PROOF: each state and event is made of constructors, so each turn start
# reduces to its state.

import Base
import ../../bend/undo.bend as U
import ../../laws/undo.bend as Undo


def Undo.undo_turn_any_state(t, live, f):
  ({==}, {==})
