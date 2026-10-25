# eukhe: the proof of LAW err_text_entry_unknown_rule
#
# PROOF: the rule tag 6 + n reads as itself when it fits and as Bad when
# too long (ws_nat_read); both ways the rule is Bad, so the request is
# malformed.

import Base
import ../../bend/err_text.bend as E
import ../../bend/ffi_err_text.bend as FE
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/err_text.bend as ErrText
import ../wire/base/spell.bend as LAWireSpell

def etu.bad(b: Bool, -n: Nat, -rest: String) -> {FE.get_rule.tag(LAWireSpell.ws_nat_answer(b, 6n+n, rest)) == Wr.Bad{} : Wr.Dec<E.Rule>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ErrText.err_text_entry_unknown_rule(n, rest):
  +x = Wr.put_nat(6n+n, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest), LAWireSpell.ws_nat_read(6n+n, rest)) : {FE.ffi.got(FE.get_req.rule(FE.get_rule.tag(_))) == Wr.err("err_text: malformed request") : String}
  %Equal.sym(Wr.Dec<E.Rule>, FE.get_rule.tag(LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest)), Wr.Bad{}, etu.bad(LawsBase.wire_fits(6n+n), n, rest)) : {FE.ffi.got(FE.get_req.rule(_)) == Wr.err("err_text: malformed request") : String}
  {==}
