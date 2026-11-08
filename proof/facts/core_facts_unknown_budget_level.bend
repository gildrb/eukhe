# eukhe: the proof of LAW core_facts_unknown_budget_level
#
# PROOF: the grammar's spelling is the entry's writer (LA.fs.*); the rule
# and the user's budgets that fit read back (LA.pc.f_mbudgets,
# LA.pc.f_customs); the budget level tag reads as itself or Bad
# (ws_nat_read), and a tag of 4 or more is no level: Bad, the malformed
# error form.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts/budgets.bend as FactsBudgets
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA

def fub.bad(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FFx.get_lv.go(LAWireSpell.ws_nat_answer(b, 4n+n, rest)) : Wr.Dec<Fx.Lv>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fub.main(+rule: Maybe<&2, Fx.Budgets>, +c: Fx.Customs, fits: {Bool.and(FactsBudgets.core_mbudgets_fit(rule), FactsBudgets.core_customs_fit(c)) == True{} : Bool}, +n: Nat, +rest: String) -> {FFx.ffi(Wr.put_nat(3n, FactsBudgets.facts_spell_mbudgets(rule, FactsBudgets.facts_spell_customs(c, Wr.put_nat(4n+n, rest))))) == Wr.err("budget request: malformed") : String}:
  +fs = fits
  %LA.fs.mbudgets(rule, FactsBudgets.facts_spell_customs(c, Wr.put_nat(4n+n, rest))) : {FFx.ffi(Wr.put_nat(3n, _)) == Wr.err("budget request: malformed") : String}
  %LA.fs.customs(c, Wr.put_nat(4n+n, rest)) : {FFx.ffi(Wr.put_nat(3n, FFx.put_mbudgets(rule, _))) == Wr.err("budget request: malformed") : String}
  %LA.pc.f_mbudgets(rule, FFx.put_customs(c, Wr.put_nat(4n+n, rest)), LLogicBool.wr_and_l(FactsBudgets.core_mbudgets_fit(rule), FactsBudgets.core_customs_fit(c), fs)) : {FFx.ffi.go(FFx.get_google.of(FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.seq(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~FFx.get_customs, _)))) == Wr.err("budget request: malformed") : String}
  %LA.pc.f_customs(c, Wr.put_nat(4n+n, rest), LLogicBool.wr_and_r(FactsBudgets.core_mbudgets_fit(rule), FactsBudgets.core_customs_fit(c), fs)) : {FFx.ffi.go(FFx.get_google.of(FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.seq.fin(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, rule, _)))) == Wr.err("budget request: malformed") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(4n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(4n+n), 4n+n, rest), LAWireSpell.ws_nat_read(4n+n, rest)) : {FFx.ffi.go(FFx.get_google.of(FFx.seq.fin(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, FFx.P2{rule, c}, FFx.get_lv.go(_)))) == Wr.err("budget request: malformed") : String}
  %fub.bad(LawsBase.wire_fits(4n+n), n, rest) : {FFx.ffi.go(FFx.get_google.of(FFx.seq.fin(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, FFx.P2{rule, c}, _))) == Wr.err("budget request: malformed") : String}
  {==}

def FactsBudgets.core_facts_unknown_budget_level(rule, c, fits, n, rest):
  fub.main(rule, c, fits, n, rest)
