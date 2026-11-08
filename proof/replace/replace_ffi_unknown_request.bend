# eukhe: the proof of LAW replace_ffi_unknown_request
#
# PROOF of LAW replace_ffi_unknown_request: the request tag 2 + n reads
# as itself when it fits and as Bad when too long (ws_nat_read); both
# ways the request is Bad, so the entry answers the malformed error.

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/replace.bend as Replace
import ../wire/base/spell.bend as LAWireSpell

def rfu.req(b: Bool, -n: Nat, -rest: String) -> {FRp.ffi.of(FRp.get_req.of(LAWireSpell.ws_nat_answer(b, 2n+n, rest))) == Wr.err("replace: malformed request") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Replace.replace_ffi_unknown_request(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FRp.ffi.of(FRp.get_req.of(_)) == Wr.err("replace: malformed request") : String}
  rfu.req(LawsBase.wire_fits(2n+n), n, rest)
