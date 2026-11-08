# eukhe: the proof of LAW core_facts_unknown_cap
#
# PROOF: the request tag 2 reads; the caller's cap tag reads as itself or Bad
# (ws_nat_read), and a tag of 2 or more is no presence: Bad, the malformed
# error form.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def fuc.bad(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FFx.get_mnat.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fuc.main(+n: Nat, +rest: String) -> {FFx.ffi(Wr.put_nat(2n, Wr.put_nat(2n+n, rest))) == Wr.err("budget request: malformed") : String}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FFx.ffi.go(FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, FFx.seq(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, FFx.get_mnat.go(_)))))))) == Wr.err("budget request: malformed") : String}
  %fuc.bad(LawsBase.wire_fits(2n+n), n, rest) : {FFx.ffi.go(FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, FFx.seq(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, _))))))) == Wr.err("budget request: malformed") : String}
  {==}

def Facts.core_facts_unknown_cap(n, rest):
  fuc.main(n, rest)
