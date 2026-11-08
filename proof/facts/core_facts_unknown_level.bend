# eukhe: the proof of LAW core_facts_unknown_level
#
# PROOF: the request tag 0 reads; the level tag reads as itself or Bad
# (ws_nat_read), and a tag of 6 or more is no level: Bad, the malformed
# error form.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def ful.bad(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FFx.get_elv.go(LAWireSpell.ws_nat_answer(b, 6n+n, rest)) : Wr.Dec<Fx.ELv>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ful.main(+n: Nat, +rest: String) -> {FFx.ffi(Wr.put_nat(0n, Wr.put_nat(6n+n, rest))) == Wr.err("budget request: malformed") : String}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(6n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest), LAWireSpell.ws_nat_read(6n+n, rest)) : {FFx.ffi.go(FFx.get_level.of(FFx.seq(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~Fx.ELv, ~Fx.Customs, ~FFx.get_customs, FFx.get_elv.go(_))))) == Wr.err("budget request: malformed") : String}
  %ful.bad(LawsBase.wire_fits(6n+n), n, rest) : {FFx.ffi.go(FFx.get_level.of(FFx.seq(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~Fx.ELv, ~Fx.Customs, ~FFx.get_customs, _)))) == Wr.err("budget request: malformed") : String}
  {==}

def Facts.core_facts_unknown_level(n, rest):
  ful.main(n, rest)
