# eukhe: the proof of LAW dmw_ffi_left_over_spelled
#
# PROOF: the spelled request is the entry's encoding (LS.dms.req), whose
# input left over answers the error form (dmw_left_over).

import Base
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel
import ./base/spell.bend as LS
import ./dmw_left_over.bend as PDmwLeftOver

def DefaultModel.dmw_ffi_left_over_spelled(x, fits, c, t):
  %LS.dms.req(x, SCon{c, t}) : {FDm.ffi(_) == Wr.err("default_model: input left over") : String}
  DefaultModel.dmw_left_over(x, c, t, fits)
