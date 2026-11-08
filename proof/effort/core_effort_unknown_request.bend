# eukhe: the proof of LAW core_effort_unknown_request
#
# PROOF: the request tag reads as itself or Bad (ws_nat_read), and a tag
# of 3 or more is no request: Bad, the malformed error form.

import Base
import ../../bend/ffi_effort.bend as FEf
import ../../bend/wire.bend as Wr
import ../../laws/effort/ladder.bend as EffortLadder
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def eu.bad(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FEf.get_req.go(LAWireSpell.ws_nat_answer(b, 3n+n, rest)) : Wr.Dec<FEf.Req>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def EffortLadder.core_effort_unknown_request(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, rest), LAWireSpell.ws_nat_read(3n+n, rest)) : {FEf.ffi.go(FEf.get_req.go(_)) == Wr.err("ladder request: malformed") : String}
  %eu.bad(LawsBase.wire_fits(3n+n), n, rest) : {FEf.ffi.go(_) == Wr.err("ladder request: malformed") : String}
  {==}
