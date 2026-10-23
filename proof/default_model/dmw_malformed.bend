# eukhe: the proof of LAW dmw_malformed

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel

def DefaultModel.dmw_malformed(s, h):
  %Equal.sym(Wr.Dec<Dm.In>, FDm.get_in(s), Wr.Bad{}, h) : {FDm.ffi.go(_) == Wr.err("default_model: malformed request") : String}
  {==}
