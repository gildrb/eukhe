# eukhe: the proof of LAW arg_repair_entry_refuses
#
# PROOF: every answer opens with a Nat, never 'E' (ae.answer_ok); so an
# answer that opens with 'E' is the one error form.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../bend/ffi_arg_repair.bend as FAr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/arg_repair.bend as ArgRepair
import ./base/entry.bend as AE
import ./base.bend as AB

def are.refuse(d: Wr.Dec<FAr.Req>, bad: {LawsBase.wire_opens_err(FAr.ffi.got(d)) == True{} : Bool}) -> {FAr.ffi.got(d) == Wr.err("arg_repair: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          AB.ab.absurd_tf({FAr.answer(q) == Wr.err("arg_repair: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FAr.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FAr.answer(q)), True{}, bad), AE.ae.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def ArgRepair.arg_repair_entry_refuses(s, bad):
  are.refuse(FAr.get_req(s), bad)
