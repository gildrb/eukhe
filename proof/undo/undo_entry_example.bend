# eukhe: the proof of LAW undo_entry_example
#
# PROOF: closed: both sides compute.

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def Undo.undo_entry_example():
  {==}
