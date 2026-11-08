# eukhe: the proof of LAW mrw_entry_spec
#
# PROOF: the spec's spelling of a request is the entry's encoding
# (LMS.mrb.in), which the entry answers with the code's table, encoded
# (mrw_answers); that reply is the spec's (LMS.mrb.reply: the list writer
# spells the count then each row, Wire.wire_list_spells_items; each row's
# tag and source are the spec's, LMS.mrb.own for the own setting).

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_roles.bend as ModelRoles
import ./base/spec.bend as LMS
import ./mrw_answers.bend as PMrwAnswers

def ModelRoles.mrw_entry_spec(x, h):
  %LMS.mrb.in(x, "") : {FMr.ffi(_) == ModelRoles.mrs_w_reply(x) : String}
  Equal.trans(String, FMr.ffi(FMr.put_in(x, "")), FMr.put_res(Mr.resolve(x), ""), ModelRoles.mrs_w_reply(x), ModelRoles.mrw_answers(x, h), LMS.mrb.reply(x))
