# eukhe: the proof of LAW cron_entry_answers
# Each request the laws spell reads back field by field (the fact:
# LCe.crr.fact; a Bool: LCe.crr.bool; a Nat that fits: LWire.pw6.nat), and
# the entry's answer to the request read is the laws' reply (LAn.cran.answer:
# each decision is its spec, and the entry's writers write the laws'
# spelling).

import Base
import ../../bend/cron_store.bend as CS
import ../../bend/ffi_cron.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/cron.bend as Cron
import ../base/wire.bend as LWire
import ./base/answer.bend as LAn
import ./base/entry.bend as LCe

def cra.take(+f: CS.Fact, +c: Bool, +d: Nat, +n: Nat, +fits: {Cron.ask_fits(CS.AskTake{f, c, d, n}) == True{} : Bool}) -> {FC.ffi(Cron.spell_ask(CS.AskTake{f, c, d, n})) == Cron.spell_answer(CS.AskTake{f, c, d, n}) : String}:
  +rest = Bool.and(LawsBase.wire_fits(d), LawsBase.wire_fits(n))
  +fr = LCe.cre.and_r(Cron.fact_fits(f), rest, fits)
  %LCe.crr.fact(f, Wr.put_bool(c, Wr.put_nat(d, Wr.put_nat(n, ""))), LCe.cre.and_l(Cron.fact_fits(f), rest, fits)) : {FC.run(FC.get_take(_)) == Cron.spell_answer(CS.AskTake{f, c, d, n}) : String}
  %LCe.crr.bool(c, Wr.put_nat(d, Wr.put_nat(n, ""))) : {FC.run(FC.get_take.claimed(f, _)) == Cron.spell_answer(CS.AskTake{f, c, d, n}) : String}
  %LWire.pw6.nat(d, Wr.put_nat(n, ""), LCe.cre.and_l(LawsBase.wire_fits(d), LawsBase.wire_fits(n), fr)) : {FC.run(FC.get_take.due(f, c, _)) == Cron.spell_answer(CS.AskTake{f, c, d, n}) : String}
  %LWire.pw6.nat(n, "", LCe.cre.and_r(LawsBase.wire_fits(d), LawsBase.wire_fits(n), fr)) : {FC.run(FC.get_take.now(f, c, d, _)) == Cron.spell_answer(CS.AskTake{f, c, d, n}) : String}
  LAn.cran.answer(CS.AskTake{f, c, d, n})

def cra.clear(w: CS.Who) -> {FC.ffi(Cron.spell_ask(CS.AskClear{w})) == Cron.spell_answer(CS.AskClear{w}) : String}:
  match w:
    case CS.Mine{b}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case CS.Theirs{b}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def cra.recover(+f: CS.Fact, +c: Bool, +fits: {Cron.ask_fits(CS.AskRecover{f, c}) == True{} : Bool}) -> {FC.ffi(Cron.spell_ask(CS.AskRecover{f, c})) == Cron.spell_answer(CS.AskRecover{f, c}) : String}:
  %LCe.crr.fact(f, Wr.put_bool(c, ""), fits) : {FC.run(FC.get_recover(_)) == Cron.spell_answer(CS.AskRecover{f, c}) : String}
  %LCe.crr.bool(c, "") : {FC.run(FC.get_recover.cleared(f, _)) == Cron.spell_answer(CS.AskRecover{f, c}) : String}
  LAn.cran.answer(CS.AskRecover{f, c})

def cra.finish(+f: CS.Fact, +r: Bool, +b: Bool, +n: Nat, +fits: {Cron.ask_fits(CS.AskFinish{f, r, b, n}) == True{} : Bool}) -> {FC.ffi(Cron.spell_ask(CS.AskFinish{f, r, b, n})) == Cron.spell_answer(CS.AskFinish{f, r, b, n}) : String}:
  %LCe.crr.fact(f, Wr.put_bool(r, Wr.put_bool(b, Wr.put_nat(n, ""))), LCe.cre.and_l(Cron.fact_fits(f), LawsBase.wire_fits(n), fits)) : {FC.run(FC.get_finish(_)) == Cron.spell_answer(CS.AskFinish{f, r, b, n}) : String}
  %LCe.crr.bool(r, Wr.put_bool(b, Wr.put_nat(n, ""))) : {FC.run(FC.get_finish.ran(f, _)) == Cron.spell_answer(CS.AskFinish{f, r, b, n}) : String}
  %LCe.crr.bool(b, Wr.put_nat(n, "")) : {FC.run(FC.get_finish.failed(f, r, _)) == Cron.spell_answer(CS.AskFinish{f, r, b, n}) : String}
  %LWire.pw6.nat(n, "", LCe.cre.and_r(Cron.fact_fits(f), LawsBase.wire_fits(n), fits)) : {FC.run(FC.get_finish.now(f, r, b, _)) == Cron.spell_answer(CS.AskFinish{f, r, b, n}) : String}
  LAn.cran.answer(CS.AskFinish{f, r, b, n})

def cra.cancel(+f: CS.Fact, +fits: {Cron.ask_fits(CS.AskCancel{f}) == True{} : Bool}) -> {FC.ffi(Cron.spell_ask(CS.AskCancel{f})) == Cron.spell_answer(CS.AskCancel{f}) : String}:
  %LCe.crr.fact(f, "", fits) : {FC.run(FC.get_cancel(_)) == Cron.spell_answer(CS.AskCancel{f}) : String}
  LAn.cran.answer(CS.AskCancel{f})

def cra.resume(+f: CS.Fact, +n: Nat, +fits: {Cron.ask_fits(CS.AskResume{f, n}) == True{} : Bool}) -> {FC.ffi(Cron.spell_ask(CS.AskResume{f, n})) == Cron.spell_answer(CS.AskResume{f, n}) : String}:
  %LCe.crr.fact(f, Wr.put_nat(n, ""), LCe.cre.and_l(Cron.fact_fits(f), LawsBase.wire_fits(n), fits)) : {FC.run(FC.get_resume(_)) == Cron.spell_answer(CS.AskResume{f, n}) : String}
  %LWire.pw6.nat(n, "", LCe.cre.and_r(Cron.fact_fits(f), LawsBase.wire_fits(n), fits)) : {FC.run(FC.get_resume.now(f, _)) == Cron.spell_answer(CS.AskResume{f, n}) : String}
  LAn.cran.answer(CS.AskResume{f, n})

def cra.halt(+f: CS.Fact, h: CS.Halt, +fits: {Cron.ask_fits(CS.AskHalt{f, h}) == True{} : Bool}) -> {FC.ffi(Cron.spell_ask(CS.AskHalt{f, h})) == Cron.spell_answer(CS.AskHalt{f, h}) : String}:
  match h:
    case CS.HPause{}:
      %LCe.crr.fact(f, Cron.spell_how(CS.HPause{}, ""), fits) : {FC.run(FC.get_halt(_)) == Cron.spell_answer(CS.AskHalt{f, CS.HPause{}}) : String}
      LAn.cran.answer(CS.AskHalt{f, CS.HPause{}})
    case CS.HStop{}:
      %LCe.crr.fact(f, Cron.spell_how(CS.HStop{}, ""), fits) : {FC.run(FC.get_halt(_)) == Cron.spell_answer(CS.AskHalt{f, CS.HStop{}}) : String}
      LAn.cran.answer(CS.AskHalt{f, CS.HStop{}})
    case CS.HDelete{}:
      %LCe.crr.fact(f, Cron.spell_how(CS.HDelete{}, ""), fits) : {FC.run(FC.get_halt(_)) == Cron.spell_answer(CS.AskHalt{f, CS.HDelete{}}) : String}
      LAn.cran.answer(CS.AskHalt{f, CS.HDelete{}})

def cra.edit(+f: CS.Fact, +m: Maybe<&2, Nat>, +fits: {Cron.ask_fits(CS.AskEdit{f, m}) == True{} : Bool}) -> {FC.ffi(Cron.spell_ask(CS.AskEdit{f, m})) == Cron.spell_answer(CS.AskEdit{f, m}) : String}:
  %LCe.crr.fact(f, Cron.spell_mnat(m, ""), LCe.cre.and_l(Cron.fact_fits(f), LawsBase.core_mfits(m), fits)) : {FC.run(FC.get_edit(_)) == Cron.spell_answer(CS.AskEdit{f, m}) : String}
  %LCe.crr.mnat(m, "", LCe.cre.and_r(Cron.fact_fits(f), LawsBase.core_mfits(m), fits)) : {FC.run(FC.get_edit.at(f, _)) == Cron.spell_answer(CS.AskEdit{f, m}) : String}
  LAn.cran.answer(CS.AskEdit{f, m})

def cra.make(+n: Nat, +fits: {Cron.ask_fits(CS.AskMake{n}) == True{} : Bool}) -> {FC.ffi(Cron.spell_ask(CS.AskMake{n})) == Cron.spell_answer(CS.AskMake{n}) : String}:
  %LWire.pw6.nat(n, "", fits) : {FC.run(FC.get_make(_)) == Cron.spell_answer(CS.AskMake{n}) : String}
  LAn.cran.answer(CS.AskMake{n})

def cra.open(b: Bool) -> {FC.ffi(Cron.spell_ask(CS.AskOpen{b})) == Cron.spell_answer(CS.AskOpen{b}) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Cron.cron_entry_answers(a, fits):
  match a:
    case CS.AskTake{f, c, d, n}:
      cra.take(f, c, d, n, fits)
    case CS.AskClear{w}:
      cra.clear(w)
    case CS.AskRecover{f, c}:
      cra.recover(f, c, fits)
    case CS.AskFinish{f, r, b, n}:
      cra.finish(f, r, b, n, fits)
    case CS.AskCancel{f}:
      cra.cancel(f, fits)
    case CS.AskResume{f, n}:
      cra.resume(f, n, fits)
    case CS.AskHalt{f, h}:
      cra.halt(f, h, fits)
    case CS.AskEdit{f, m}:
      cra.edit(f, m, fits)
    case CS.AskMake{n}:
      cra.make(n, fits)
    case CS.AskOpen{b}:
      cra.open(b)
