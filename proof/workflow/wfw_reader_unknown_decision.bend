# eukhe: the proof of LAW wfw_reader_unknown_decision
#
# PROOF: the decision tag reads as itself or Bad (ws_nat_read); a tag of 5
# or more is no decision: Bad.

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../bend/workflow.bend as W
import ../../laws/workflow/model.bend as Workflow
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def wrud.bad(b: Bool, -n: Nat, -rest: String) -> {FW.get_admit.go(LAWireSpell.ws_nat_answer(b, 5n+n, rest)) == Wr.Bad{} : Wr.Dec<W.Admit>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Workflow.wfw_reader_unknown_decision(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(5n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(5n+n), 5n+n, rest), LAWireSpell.ws_nat_read(5n+n, rest)) : {FW.get_admit.go(_) == Wr.Bad{} : Wr.Dec<W.Admit>}
  wrud.bad(LawsBase.wire_fits(5n+n), n, rest)
