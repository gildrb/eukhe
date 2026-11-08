# eukhe: the proof of LAW mrw_left_over

import Base
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/model_roles.bend as ModelRoles
import ./base.bend as LA

def ModelRoles.mrw_left_over(x, c, rest, h):
  %LA.pmr.in(x, SCon{c, rest}, h) : {FMr.ffi.go(_) == Wr.err("model_roles: input left over") : String}
  {==}
