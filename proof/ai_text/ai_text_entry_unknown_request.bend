# eukhe: the proof of LAW ai_text_entry_unknown_request
#
# PROOF: the tag 5 + n reads as itself when it fits and as Bad when too
# long (ws_nat_read); both ways the request is Bad.

import Base
import ../../bend/ffi_ai_text.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/ai_text.bend as AiText
import ../wire/base/spell.bend as LAWireSpell

def aitu.bad(b: Bool, -n: Nat, -rest: String) -> {FT.get_req.tag(LAWireSpell.ws_nat_answer(b, 5n+n, rest)) == Wr.Bad{} : Wr.Dec<FT.Req>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def AiText.ai_text_entry_unknown_request(n, rest):
  +x = Wr.put_nat(5n+n, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(5n+n), 5n+n, rest), LAWireSpell.ws_nat_read(5n+n, rest)) : {FT.ffi.got(FT.get_req.tag(_)) == Wr.err("ai_text: malformed request") : String}
  %Equal.sym(Wr.Dec<FT.Req>, FT.get_req.tag(LAWireSpell.ws_nat_answer(LawsBase.wire_fits(5n+n), 5n+n, rest)), Wr.Bad{}, aitu.bad(LawsBase.wire_fits(5n+n), n, rest)) : {FT.ffi.got(_) == Wr.err("ai_text: malformed request") : String}
  {==}
