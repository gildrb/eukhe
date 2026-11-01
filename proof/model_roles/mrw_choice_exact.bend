# eukhe: the proof of LAW mrw_choice_exact

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/model_roles.bend as ModelRoles
import ./base/exact.bend as LX

def ModelRoles.mrw_choice_exact(s, c, rest, h):
  LX.mx.choice(Wr.get_nat(s), s, c, rest, {==}, h)
