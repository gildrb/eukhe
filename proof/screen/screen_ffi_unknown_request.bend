# eukhe: the proof of LAW screen_ffi_unknown_request
#
# PROOF: the request tag reads as itself or Bad (ws_nat_read); a tag of 4
# or more is no request: Bad, the malformed error form.

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/screen.bend as Screen
import ../wire/base/spell.bend as LAWireSpell

def sur.at(b: Bool, +n: Nat, rest: String) -> {FSc.ffi.of(FSc.get_req.of(LAWireSpell.ws_nat_answer(b, 4n+n, rest))) == Wr.err("screen: malformed request") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Screen.screen_ffi_unknown_request(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(4n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(4n+n), 4n+n, rest), LAWireSpell.ws_nat_read(4n+n, rest)) : {FSc.ffi.of(FSc.get_req.of(_)) == Wr.err("screen: malformed request") : String}
  sur.at(LawsBase.wire_fits(4n+n), n, rest)
