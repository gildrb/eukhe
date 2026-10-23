# eukhe: the proof of LAW dmw_left_over

import Base
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel
import ./base.bend as LA

def DefaultModel.dmw_left_over(x, c, rest, h):
  %LA.pdw.in(x, SCon{c, rest}, h) : {FDm.ffi.go(_) == Wr.err("default_model: input left over") : String}
  {==}
