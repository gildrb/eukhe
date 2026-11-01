# eukhe: the proof of LAW model_name_entry_unknown_request
#
# PROOF: the request tag 2 + n reads as itself when it fits and as Bad when
# too long (ws_nat_read); both ways the request is Bad.

import Base
import ../../bend/ffi_model_name.bend as FM
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_name.bend as ModelName
import ../wire/base/spell.bend as LAWireSpell

def mnu.bad(b: Bool, -n: Nat, -rest: String) -> {FM.get_req.tag(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) == Wr.Bad{} : Wr.Dec<FM.Req>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ModelName.model_name_entry_unknown_request(n, rest):
  +x = Wr.put_nat(2n+n, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FM.ffi.got(FM.get_req.tag(_)) == Wr.err("model_name: malformed request") : String}
  %Equal.sym(Wr.Dec<FM.Req>, FM.get_req.tag(LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest)), Wr.Bad{}, mnu.bad(LawsBase.wire_fits(2n+n), n, rest)) : {FM.ffi.got(_) == Wr.err("model_name: malformed request") : String}
  {==}
