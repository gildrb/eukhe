# eukhe: the proof of LAW dash_access_entry_refuses
#
# PROOF: the entry answers either a verdict, a Bool (never 'E':
# wire_bool_not_err), or the one error form; so an answer that opens with
# 'E' is that error form.

import Base
import ../../bend/dash_access.bend as Ac
import ../../bend/ffi_dash_access.bend as FAc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash_access.bend as DashAccess
import ../../laws/wire.bend as Wire
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ../base/staging.bend as LStg

def daf.answer_ok(q: FAc.Req) -> {LawsBase.wire_opens_err(FAc.answer(q)) == False{} : Bool}:
  match q:
    case FAc.QHost{hh, al}:
      Wire.wire_bool_not_err(Ac.host_allowed(hh, al), "")
    case FAc.QOrigin{o, hh}:
      Wire.wire_bool_not_err(Ac.same_origin(o, hh), "")

def daf.refuse(d: Wr.Dec<FAc.Req>, bad: {LawsBase.wire_opens_err(FAc.ffi.got(d)) == True{} : Bool}) -> {FAc.ffi.got(d) == Wr.err("dash_access: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FAc.answer(q) == Wr.err("dash_access: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FAc.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FAc.answer(q)), True{}, bad), daf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def DashAccess.dash_access_entry_refuses(s, bad):
  daf.refuse(FAc.get_req(s), bad)
