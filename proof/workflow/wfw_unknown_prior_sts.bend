# eukhe: the proof of LAW wfw_unknown_prior_sts
#
# PROOF: the kind 0 and the prior tag 1 read back (the Nat round trip);
# the status tag reads as itself or Bad (ws_nat_read), and a tag of 6 or
# more is no status: Bad, the malformed error form.

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../laws/workflow/model.bend as Workflow
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA

def wups.bad(b: Bool, -n: Nat, -rest: String) -> {FW.ffi.go(FW.get_req.admit(FW.get_prior.some(FW.get_sts.go(LAWireSpell.ws_nat_answer(b, 6n+n, rest))))) == Wr.err("workflow: malformed request") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Workflow.wfw_unknown_prior_sts(n, rest):
  %LA.pww.nat(0n, Wr.put_nat(1n, Wr.put_nat(6n+n, rest)), {==}) : {FW.ffi.go(FW.get_req.go(_)) == Wr.err("workflow: malformed request") : String}
  %LA.pww.nat(1n, Wr.put_nat(6n+n, rest), {==}) : {FW.ffi.go(FW.get_req.admit(FW.get_prior.go(_))) == Wr.err("workflow: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(6n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest), LAWireSpell.ws_nat_read(6n+n, rest)) : {FW.ffi.go(FW.get_req.admit(FW.get_prior.some(FW.get_sts.go(_)))) == Wr.err("workflow: malformed request") : String}
  wups.bad(LawsBase.wire_fits(6n+n), n, rest)
