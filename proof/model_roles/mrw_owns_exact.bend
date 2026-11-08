# eukhe: the proof of LAW mrw_owns_exact

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/model_roles.bend as ModelRoles
import ./base/exact.bend as LX

def ModelRoles.mrw_owns_exact(s, o, rest, h):
  LX.mx.owns_0(FMr.get_choice(s), s, o, rest, {==}, h)
