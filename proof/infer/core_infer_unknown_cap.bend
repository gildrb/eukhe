# eukhe: the proof of LAW core_infer_unknown_cap
#
# PROOF: the cap tag reads as itself or Bad (ws_nat_read), and a tag of 2
# or more is no cap: Bad, the malformed error form.

import Base
import ../../bend/ffi_infer.bend as FIn
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/infer.bend as Infer
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def iu.bad(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FIn.seq(~FIn.P2<Maybe<&2, Nat>, List<&2, If.ToolPrio>>, ~List<&2, Nat>, ~FIn.get_ids, FIn.seq(~Maybe<&2, Nat>, ~List<&2, If.ToolPrio>, ~FIn.get_tools, FIn.get_mnat.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)))) : Wr.Dec<FIn.P2<FIn.P2<Maybe<&2, Nat>, List<&2, If.ToolPrio>>, List<&2, Nat>>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Infer.core_infer_unknown_cap(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FIn.ffi.go(FIn.get_req.of(FIn.seq(~FIn.P2<Maybe<&2, Nat>, List<&2, If.ToolPrio>>, ~List<&2, Nat>, ~FIn.get_ids, FIn.seq(~Maybe<&2, Nat>, ~List<&2, If.ToolPrio>, ~FIn.get_tools, FIn.get_mnat.go(_))))) == Wr.err("strict plan request: malformed") : String}
  %iu.bad(LawsBase.wire_fits(2n+n), n, rest) : {FIn.ffi.go(FIn.get_req.of(_)) == Wr.err("strict plan request: malformed") : String}
  {==}
