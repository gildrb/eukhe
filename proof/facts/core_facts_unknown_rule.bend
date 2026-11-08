# eukhe: the proof of LAW core_facts_unknown_rule
#
# PROOF: the request tag 3 reads; the rule tag reads as itself or Bad
# (ws_nat_read), and a tag of 2 or more is no presence: Bad, the malformed
# error form.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def furu.bad(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FFx.get_mbudgets.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) : Wr.Dec<Maybe<&2, Fx.Budgets>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def furu.main(+n: Nat, +rest: String) -> {FFx.ffi(Wr.put_nat(3n, Wr.put_nat(2n+n, rest))) == Wr.err("budget request: malformed") : String}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FFx.ffi.go(FFx.get_google.of(FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.seq(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~FFx.get_customs, FFx.get_mbudgets.go(_))))) == Wr.err("budget request: malformed") : String}
  %furu.bad(LawsBase.wire_fits(2n+n), n, rest) : {FFx.ffi.go(FFx.get_google.of(FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.seq(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~FFx.get_customs, _)))) == Wr.err("budget request: malformed") : String}
  {==}

def Facts.core_facts_unknown_rule(n, rest):
  furu.main(n, rest)
