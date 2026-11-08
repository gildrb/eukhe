# eukhe: the proof of LAW family_entry_malformed_exact
#
# PROOF: every answer opens with a Nat, never 'E' (fe.answer_ok); so an answer that opens with 'E' is the one error form.

import Base
import ../../bend/family.bend as F
import ../../bend/ffi_family.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/family.bend as Family
import ./base/entry.bend as LE
import ../base/staging.bend as LStg


def ff.refuse(x: Wr.Dec<FF.Req>, bad: {LawsBase.wire_opens_err(FF.ffi.got(x)) == True{} : Bool}) -> {FF.ffi.got(x) == Wr.err("family: malformed request") : String}:
  match x:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FF.answer(q) == Wr.err("family: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FF.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FF.answer(q)), True{}, bad), LE.fe.answer_ok(q)))
        case SCon{y, z}:
          {==}
    case Wr.Bad{}:
      {==}

def Family.family_entry_malformed_exact(s, bad):
  ff.refuse(FF.get_req(s), bad)
