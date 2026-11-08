# eukhe: the proof of LAW mrw_entry_exact
#
# PROOF: a decoder answer Got{x, r} means the input is the spec's
# spelling of x before r, with x within the wire (LME.mee.rp); the entry
# answers a value only for r empty: a left-over or malformed input answers
# the error form.

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_roles.bend as ModelRoles
import ../base/staging.bend as LStg
import ./base/entry.bend as LME

def mee.Goal(s: String) -> Type:
  Sigma<&1, &1, Mr.In, x => {s == ModelRoles.mrs_w_in(x, "") : String} & {ModelRoles.mrw_in_fits(x) == True{} : Bool}>

def mee.top(-s: String, d: Wr.Dec<Mr.In>, rp: LME.mee.RP(s, d), ok: {LawsBase.wire_opens_err(FMr.ffi.go(d)) == False{} : Bool}) -> mee.Goal(s):
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          (x, rp)
        case SCon{c, t}:
          LStg.stg.absurd(mee.Goal(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(mee.Goal(s), ok)

def ModelRoles.mrw_entry_exact(s, ok):
  mee.top(s, FMr.get_in(s), LME.mee.rp(s, FMr.get_in(s), {==}), ok)
