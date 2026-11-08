# eukhe: the proof of LAW kin_entry_malformed_exact
#
# PROOF: every answer opens with a Nat, never 'E' (ke.answer_ok); so an answer that opens with 'E' is the one error form.

import Base
import ../../bend/kin.bend as K
import ../../bend/ffi_kin.bend as FK
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/kin.bend as Kin
import ./base/entry.bend as LE
import ../base/staging.bend as LStg


def kf.refuse(x: Wr.Dec<FK.Req>, bad: {LawsBase.wire_opens_err(FK.ffi.got(x)) == True{} : Bool}) -> {FK.ffi.got(x) == Wr.err("kin: malformed request") : String}:
  match x:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FK.answer(q) == Wr.err("kin: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FK.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FK.answer(q)), True{}, bad), LE.ke.answer_ok(q)))
        case SCon{y, z}:
          {==}
    case Wr.Bad{}:
      {==}

def Kin.kin_entry_malformed_exact(s, bad):
  kf.refuse(FK.get_req(s), bad)
