# eukhe: the proof of LAW path_own_entry_refuses
#
# PROOF: the entry answers either the model's answer, which opens with a
# Nat (never 'E': LA.po.answer_ok), or the one error form; so an answer
# that opens with 'E' is that error form.

import Base
import ../../bend/ffi_path_own.bend as FPo
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/path_own.bend as PathOwn
import ../base/staging.bend as LStg
import ./base.bend as LA

def pof.refuse(d: Wr.Dec<FPo.Req>, bad: {LawsBase.wire_opens_err(FPo.run(d)) == True{} : Bool}) -> {FPo.run(d) == Wr.err("path_own: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FPo.answer(q) == Wr.err("path_own: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FPo.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FPo.answer(q)), True{}, bad), LA.po.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def PathOwn.path_own_entry_refuses(s, bad):
  pof.refuse(FPo.get_req(s), bad)
