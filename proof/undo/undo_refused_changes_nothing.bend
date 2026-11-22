# eukhe: the proof of LAW undo_refused_changes_nothing
#
# PROOF: closed for each first snapshot: the model computes both sides.

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def Undo.undo_refused_changes_nothing(b):
  {==}
