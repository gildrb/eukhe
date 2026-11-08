# eukhe: the proof of LAW wfw_unknown_kind
#
# PROOF: the kind tag reads as itself or Bad (ws_nat_read); a tag of 2 or
# more is no kind: Bad, the malformed error form.

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../laws/workflow.bend as Workflow
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def wuk.bad(b: Bool, -n: Nat, -rest: String) -> {FW.ffi.go(FW.get_req.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest))) == Wr.err("workflow: malformed request") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Workflow.wfw_unknown_kind(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FW.ffi.go(FW.get_req.go(_)) == Wr.err("workflow: malformed request") : String}
  wuk.bad(LawsBase.wire_fits(2n+n), n, rest)
