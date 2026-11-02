# eukhe: the proof of LAW aws_text_entry_unknown_request
#
# PROOF: the tag 6 + n reads as itself when it fits and as Bad when too
# long (ws_nat_read); both ways the request is Bad.

import Base
import ../../bend/ffi_aws_text.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/aws_text.bend as AwsText
import ../wire/base/spell.bend as LAWireSpell

def awu.bad(b: Bool, -n: Nat, -rest: String) -> {FA.get_req.tag(LAWireSpell.ws_nat_answer(b, 6n+n, rest)) == Wr.Bad{} : Wr.Dec<FA.Req>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def AwsText.aws_text_entry_unknown_request(n, rest):
  +x = Wr.put_nat(6n+n, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest), LAWireSpell.ws_nat_read(6n+n, rest)) : {FA.ffi.got(FA.get_req.tag(_)) == Wr.err("aws_text: malformed request") : String}
  %Equal.sym(Wr.Dec<FA.Req>, FA.get_req.tag(LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest)), Wr.Bad{}, awu.bad(LawsBase.wire_fits(6n+n), n, rest)) : {FA.ffi.got(_) == Wr.err("aws_text: malformed request") : String}
  {==}
