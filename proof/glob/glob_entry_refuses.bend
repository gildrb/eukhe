# eukhe: the proof of LAW glob_entry_refuses
#
# PROOF: the entry answers a value that opens with a digit, T or F (ge.answer_ok), or the one error form; an answer that opens with 'E' is that error form.

import Base
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/entry.bend as GE

def Glob.glob_entry_refuses(s, bad):
  GE.ge.refuse(FG.get_req(s), bad)
