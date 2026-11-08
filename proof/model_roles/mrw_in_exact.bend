# eukhe: the proof of LAW mrw_in_exact

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/model_roles.bend as ModelRoles
import ./base/exact.bend as LX

def ModelRoles.mrw_in_exact(s, x, rest, h):
  LX.mx.in_go(FMr.get_owns(s), s, x, rest, {==}, h)
