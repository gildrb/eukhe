# eukhe: the proof of LAW core_facts_unknown_request
#
# PROOF: the request tag reads as itself or Bad (ws_nat_read); a tag of 5 or
# more is no request: Bad, the malformed error form.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def fur.bad(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FFx.get_req.go(LAWireSpell.ws_nat_answer(b, 5n+n, rest)) : Wr.Dec<FFx.Req>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fur.main(+n: Nat, +rest: String) -> {FFx.ffi(Wr.put_nat(5n+n, rest)) == Wr.err("budget request: malformed") : String}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(5n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(5n+n), 5n+n, rest), LAWireSpell.ws_nat_read(5n+n, rest)) : {FFx.ffi.go(FFx.get_req.go(_)) == Wr.err("budget request: malformed") : String}
  %fur.bad(LawsBase.wire_fits(5n+n), n, rest) : {FFx.ffi.go(_) == Wr.err("budget request: malformed") : String}
  {==}

def Facts.core_facts_unknown_request(n, rest):
  fur.main(n, rest)
