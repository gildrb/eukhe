# eukhe: the proof of LAW mrw_answers

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../laws/model_roles.bend as ModelRoles
import ./base.bend as LA

def ModelRoles.mrw_answers(x, h):
  %LA.pmr.in(x, "", h) : {FMr.ffi.go(_) == FMr.put_res(Mr.resolve(x), "") : String}
  {==}
