# eukhe: the proof of LAW dmw_answers

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.dmw_answers(x, h):
  %LA.pdw.in(x, "", h) : {FDm.ffi.go(_) == FDm.put_res(Dm.resolve(x), "") : String}
  {==}
