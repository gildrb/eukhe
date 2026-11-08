# eukhe: the proof of LAW core_facts_unknown_custom
#
# PROOF: the request tag 4 reads; the first user's budget tag reads as itself or
# Bad (ws_nat_read), and a tag of 2 or more is no presence: Bad, the
# malformed error form.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts/budgets.bend as FactsBudgets
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def fuk.bad(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FFx.get_mnat.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fuk.main(+n: Nat, +rest: String) -> {FFx.ffi(Wr.put_nat(4n, Wr.put_nat(2n+n, rest))) == Wr.err("budget request: malformed") : String}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FFx.ffi.go(FFx.get_aux.of(FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~Fx.Customs, ~Fx.Budgets, ~FFx.get_budgets, FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.get_mnat.go(_)))))))))) == Wr.err("budget request: malformed") : String}
  %fuk.bad(LawsBase.wire_fits(2n+n), n, rest) : {FFx.ffi.go(FFx.get_aux.of(FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~Fx.Customs, ~Fx.Budgets, ~FFx.get_budgets, FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, ~FFx.get_mnat, _))))))))) == Wr.err("budget request: malformed") : String}
  {==}

def FactsBudgets.core_facts_unknown_custom(n, rest):
  fuk.main(n, rest)
