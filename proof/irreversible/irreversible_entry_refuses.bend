# eukhe: the proof of LAW irreversible_entry_refuses
#
# PROOF: the entry answers either the model's answer, which opens with a
# Bool or a Nat (never 'E': LA.irb.answer_ok), or the one error form; so
# an answer that opens with 'E' is that error form.

import Base
import ../../bend/ffi_irreversible.bend as FIr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/irreversible.bend as Irreversible
import ../base/staging.bend as LStg
import ./base.bend as LA

def irf.refuse(d: Wr.Dec<FIr.Req>, bad: {LawsBase.wire_opens_err(FIr.run(d)) == True{} : Bool}) -> {FIr.run(d) == Wr.err("irreversible: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FIr.answer(q) == Wr.err("irreversible: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FIr.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FIr.answer(q)), True{}, bad), LA.irb.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Irreversible.irreversible_entry_refuses(s, bad):
  irf.refuse(FIr.get_req(s), bad)
