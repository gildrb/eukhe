# eukhe: the proof of LAW mrw_entry_left_over_spec
#
# PROOF: the spec's spelling of a request is the entry's encoding
# (LMS.mrb.in); a request encoded before more input answers the left-over
# error (mrw_left_over).

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_roles.bend as ModelRoles
import ./base/spec.bend as LMS
import ./mrw_left_over.bend as PMrwLeftOver

def ModelRoles.mrw_entry_left_over_spec(x, c, rest, h):
  %LMS.mrb.in(x, SCon{c, rest}) : {FMr.ffi(_) == Wr.err("model_roles: input left over") : String}
  ModelRoles.mrw_left_over(x, c, rest, h)
