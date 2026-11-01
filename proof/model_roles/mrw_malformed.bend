# eukhe: the proof of LAW mrw_malformed

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/model_roles.bend as ModelRoles

def ModelRoles.mrw_malformed(s, h):
  %Equal.sym(Wr.Dec<Mr.In>, FMr.get_in(s), Wr.Bad{}, h) : {FMr.ffi.go(_) == Wr.err("model_roles: malformed request") : String}
  {==}
