# eukhe: the proof of LAW mrw_entry_left_over_exact
#
# PROOF: the entry answers the left-over error only for a decoder answer
# Got{x, r} with r not empty (a table is no error, LME.mee.not_err; a
# malformed request answers another text); then the input is the spec's
# spelling of x before r, with x within the wire (LME.mee.rp).

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_roles.bend as ModelRoles
import ../base/staging.bend as LStg
import ./base/entry.bend as LME

def mle.Goal(s: String) -> Type:
  Sigma<&1, &1, Mr.In, x => Sigma<&1, &1, String, t => {s == ModelRoles.mrs_w_in(x, t) : String} & ({String.is_empty(t) == False{} : Bool} & {ModelRoles.mrw_in_fits(x) == True{} : Bool})>>

def mle.top(-s: String, d: Wr.Dec<Mr.In>, rp: LME.mee.RP(s, d), e: {FMr.ffi.go(d) == Wr.err("model_roles: input left over") : String}) -> mle.Goal(s):
  match d:
    case Wr.Got{x, rest}:
      match x:
        case Mr.In{+o, +al}:
          match rest:
            case SNil{}:
              +ne = Equal.cong(String, Bool, z => LawsBase.wire_opens_err(z), FMr.put_res(Mr.resolve(Mr.In{o, al}), ""), Wr.err("model_roles: input left over"), e)
              LStg.stg.absurdF(mle.Goal(s), Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FMr.put_res(Mr.resolve(Mr.In{o, al}), "")), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FMr.put_res(Mr.resolve(Mr.In{o, al}), "")), False{}, LME.mee.not_err(Mr.In{o, al})), ne))
            case SCon{+c, +t}:
              (p1, p2) = rp
              (Mr.In{o, al}, (SCon{c, t}, (p1, ({==}, p2))))
    case Wr.Bad{}:
      LStg.stg.absurd(mle.Goal(s), Equal.cong(String, Bool, z => String.eq(z, Wr.err("model_roles: malformed request")), Wr.err("model_roles: malformed request"), Wr.err("model_roles: input left over"), e))

def ModelRoles.mrw_entry_left_over_exact(s, e):
  mle.top(s, FMr.get_in(s), LME.mee.rp(s, FMr.get_in(s), {==}), e)
