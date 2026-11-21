# eukhe: the proof of LAW undo_takes_newest
#
# PROOF: by computation: the state and the event are constructors, so the
# model's /undo reduces to its case for a non-empty list of turns.

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def Undo.undo_takes_newest(t, rest, b):
  {==}
