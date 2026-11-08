# eukhe: lemmas of area model_roles shared by the proofs of the entry
# laws against the spec (R8): what a decoder answer says about the input
# (mrw_in_exact, LMF.mf.in), and the table answered is no error

import Base
import ../../../bend/model_roles.bend as Mr
import ../../../bend/ffi_model_roles.bend as FMr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/model_roles.bend as ModelRoles
import ../mrw_in_exact.bend as PMrwInExact
import ./spec.bend as LMS
import ./fits.bend as LMF

# the decoder's answer is the spec's spelling of what it read, before the
# rest, and what it read fits the wire
def mee.RP(s: String, d: Wr.Dec<Mr.In>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == ModelRoles.mrs_w_in(x, r) : String} & {ModelRoles.mrw_in_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mee.rp(+s: String, d: Wr.Dec<Mr.In>, +ed: {FMr.get_in(s) == d : Wr.Dec<Mr.In>}) -> mee.RP(s, d):
  match d:
    case Wr.Got{+x, +r}:
      (Equal.trans(String, s, FMr.put_in(x, r), ModelRoles.mrs_w_in(x, r), ModelRoles.mrw_in_exact(s, x, r, ed), LMS.mrb.in(x, r)), LMF.mf.in(s, x, r, ed))
    case Wr.Bad{}:
      Unit{}

# the table the entry answers is no error
def mee.not_err(x: Mr.In) -> {LawsBase.wire_opens_err(FMr.put_res(Mr.resolve(x), "")) == False{} : Bool}:
  match x:
    case Mr.In{o, al}:
      {==}
