# eukhe: the proof of LAW mrw_entry_refuses
#
# PROOF: a decoder answer Bad{} answers the malformed-request error; a
# request with input left over the left-over error; a request read whole a
# table, which is no error (LME.mee.not_err).

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_roles.bend as ModelRoles
import ../base/staging.bend as LStg
import ./base/entry.bend as LME

def mrf.Goal(s: String) -> Type:
  {s == Wr.err("model_roles: malformed request") : String} | {s == Wr.err("model_roles: input left over") : String}

def mrf.go(d: Wr.Dec<Mr.In>, bad: {LawsBase.wire_opens_err(FMr.ffi.go(d)) == True{} : Bool}) -> mrf.Goal(FMr.ffi.go(d)):
  match d:
    case Wr.Got{x, rest}:
      match x:
        case Mr.In{+o, +al}:
          match rest:
            case SNil{}:
              LStg.stg.absurdF(mrf.Goal(FMr.ffi.go(Wr.Got{Mr.In{o, al}, ""})), Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FMr.put_res(Mr.resolve(Mr.In{o, al}), "")), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FMr.put_res(Mr.resolve(Mr.In{o, al}), "")), False{}, LME.mee.not_err(Mr.In{o, al})), bad))
            case SCon{c, t}:
              Inr{{==}}
    case Wr.Bad{}:
      Inl{{==}}

def ModelRoles.mrw_entry_refuses(s, bad):
  mrf.go(FMr.get_in(s), bad)
