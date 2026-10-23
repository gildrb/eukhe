# eukhe: the proof of LAW dmw_answers

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../laws/default_model.bend as DefaultModel
import ./base.bend as LA

def DefaultModel.dmw_answers(x, h):
  %LA.pdw.in(x, "", h) : {FDm.ffi.go(_) == FDm.put_res(Dm.resolve(x), "") : String}
  {==}
