# eukhe: the proof of LAW cron_file_entry_answers
# Each request the laws spell reads back list by list and field by field
# (proof/cron_file/base/wire.bend), and the entry's answer to it is the
# laws' reply (each pass being its spec: the cron_file_*_exact laws; the
# entry's writers write the laws' spelling).
import Base
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../bend/ffi_cron_file.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/cron.bend as Cron
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ../base/wire.bend as LWire
import ./base/logic.bend as LCfl
import ../cron/base/entry.bend as LCe
import ./base/wire.bend as LCfw
import ./cron_file_take_exact.bend as PTake
import ./cron_file_recover_exact.bend as PRecover
import ./cron_file_finish_exact.bend as PFinish

def cfa.take(+js: List<&2, CF.Slot>, +cs: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat, +fits: {CronFileEntry.pass_fits(CF.PassTake{js, cs, d, n}) == True{} : Bool}) -> {FF.ffi(CronFileEntry.spell_pass(CF.PassTake{js, cs, d, n})) == CronFileEntry.spell_answer(CF.PassTake{js, cs, d, n}) : String}:
  +a = Bool.and(LawsBase.wire_fits(List.length(&2, CF.Slot, js)), CronFileEntry.slots_fit(js))
  +b = Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Maybe<&2, Nat>, cs)), CronFileEntry.keys_fit(cs)), Bool.and(LawsBase.wire_fits(d), LawsBase.wire_fits(n)))
  +fb = LCfl.cfl.and_r(a, b, fits)
  +kc = Bool.and(LawsBase.wire_fits(List.length(&2, Maybe<&2, Nat>, cs)), CronFileEntry.keys_fit(cs))
  +tm = Bool.and(LawsBase.wire_fits(d), LawsBase.wire_fits(n))
  +ft = LCfl.cfl.and_r(kc, tm, fb)
  +r2 = Wr.put_nat(d, Wr.put_nat(n, ""))
  +r1 = Wr.put_list(~Maybe<&2, Nat>, ~Cron.spell_mnat, cs, r2)
  %LCfw.cfw.slots_rt(js, r1, LCfl.cfl.and_l(a, b, fits)) : {FF.run(FF.get_take(_)) == CronFileEntry.spell_answer(CF.PassTake{js, cs, d, n}) : String}
  %LCfw.cfw.keys_rt(cs, r2, LCfl.cfl.and_l(kc, tm, fb)) : {FF.run(FF.get_take.cs(js, _)) == CronFileEntry.spell_answer(CF.PassTake{js, cs, d, n}) : String}
  %LWire.pw6.nat(d, Wr.put_nat(n, ""), LCfl.cfl.and_l(LawsBase.wire_fits(d), LawsBase.wire_fits(n), ft)) : {FF.run(FF.get_take.due(js, cs, _)) == CronFileEntry.spell_answer(CF.PassTake{js, cs, d, n}) : String}
  %LWire.pw6.nat(n, "", LCfl.cfl.and_r(LawsBase.wire_fits(d), LawsBase.wire_fits(n), ft)) : {FF.run(FF.get_take.now(js, cs, d, _)) == CronFileEntry.spell_answer(CF.PassTake{js, cs, d, n}) : String}
  %CronFile.cron_file_take_exact(js, cs, d, n) : {FF.put_tooks(CF.take(js, cs, d, n), "") == Wr.put_list(~CS.Took, ~Cron.spell_took, _, "") : String}
  LCfw.cfw.tooks(CF.take(js, cs, d, n), "")

def cfa.recover(+js: List<&2, CF.Slot>, +cs: List<&2, CF.Hold>, +fits: {CronFileEntry.pass_fits(CF.PassRecover{js, cs}) == True{} : Bool}) -> {FF.ffi(CronFileEntry.spell_pass(CF.PassRecover{js, cs})) == CronFileEntry.spell_answer(CF.PassRecover{js, cs}) : String}:
  +a = Bool.and(LawsBase.wire_fits(List.length(&2, CF.Slot, js)), CronFileEntry.slots_fit(js))
  +b = Bool.and(LawsBase.wire_fits(List.length(&2, CF.Hold, cs)), CronFileEntry.holds_fit(cs))
  +r1 = Wr.put_list(~CF.Hold, ~CronFileEntry.spell_hold, cs, "")
  %LCfw.cfw.slots_rt(js, r1, LCfl.cfl.and_l(a, b, fits)) : {FF.run(FF.get_recover(_)) == CronFileEntry.spell_answer(CF.PassRecover{js, cs}) : String}
  %LCfw.cfw.holds_rt(cs, "", LCfl.cfl.and_r(a, b, fits)) : {FF.run(FF.get_recover.cs(js, _)) == CronFileEntry.spell_answer(CF.PassRecover{js, cs}) : String}
  %CronFile.cron_file_recover_exact(js, cs) : {FF.put_swept(CF.recover(js, cs), "") == CronFileEntry.spell_swept(_) : String}
  %LCfw.cfw.backs(CF.recover.js(js, cs), "") : {FF.put_swept(CF.recover(js, cs), "") == CronFileEntry.spell_keeps(CF.keeps(cs), _) : String}
  {==}

def cfa.finish(+js: List<&2, CF.Slot>, +cs: List<&2, CF.Pin>, +r: Bool, +bb: Bool, +n: Nat, +fits: {CronFileEntry.pass_fits(CF.PassFinish{js, cs, r, bb, n}) == True{} : Bool}) -> {FF.ffi(CronFileEntry.spell_pass(CF.PassFinish{js, cs, r, bb, n})) == CronFileEntry.spell_answer(CF.PassFinish{js, cs, r, bb, n}) : String}:
  +a = Bool.and(LawsBase.wire_fits(List.length(&2, CF.Slot, js)), CronFileEntry.slots_fit(js))
  +b = Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, CF.Pin, cs)), CronFileEntry.pins_fit(cs)), LawsBase.wire_fits(n))
  +fb = LCfl.cfl.and_r(a, b, fits)
  +pc = Bool.and(LawsBase.wire_fits(List.length(&2, CF.Pin, cs)), CronFileEntry.pins_fit(cs))
  +r2 = Wr.put_bool(r, Wr.put_bool(bb, Wr.put_nat(n, "")))
  +r1 = Wr.put_list(~CF.Pin, ~CronFileEntry.spell_pin, cs, r2)
  %LCfw.cfw.slots_rt(js, r1, LCfl.cfl.and_l(a, b, fits)) : {FF.run(FF.get_finish(_)) == CronFileEntry.spell_answer(CF.PassFinish{js, cs, r, bb, n}) : String}
  %LCfw.cfw.pins_rt(cs, r2, LCfl.cfl.and_l(pc, LawsBase.wire_fits(n), fb)) : {FF.run(FF.get_finish.cs(js, _)) == CronFileEntry.spell_answer(CF.PassFinish{js, cs, r, bb, n}) : String}
  %LCe.crr.bool(r, Wr.put_bool(bb, Wr.put_nat(n, ""))) : {FF.run(FF.get_finish.ran(js, cs, _)) == CronFileEntry.spell_answer(CF.PassFinish{js, cs, r, bb, n}) : String}
  %LCe.crr.bool(bb, Wr.put_nat(n, "")) : {FF.run(FF.get_finish.failed(js, cs, r, _)) == CronFileEntry.spell_answer(CF.PassFinish{js, cs, r, bb, n}) : String}
  %LWire.pw6.nat(n, "", LCfl.cfl.and_r(pc, LawsBase.wire_fits(n), fb)) : {FF.run(FF.get_finish.now(js, cs, r, bb, _)) == CronFileEntry.spell_answer(CF.PassFinish{js, cs, r, bb, n}) : String}
  %CronFile.cron_file_finish_exact(60000n, js, cs, r, bb, n) : {FF.put_closed(CF.finish(60000n, js, cs, r, bb, n), "") == CronFileEntry.spell_closed(_) : String}
  %LCfw.cfw.fins(CF.finish.js(js, CF.hit(cs), 60000n, r, bb, n), "") : {FF.put_closed(CF.finish(60000n, js, cs, r, bb, n), "") == CronFileEntry.spell_keeps(CF.drops(cs, False{}), _) : String}
  {==}

def CronFileEntry.cron_file_entry_answers(a, fits):
  match a:
    case CF.PassTake{js, cs, d, n}:
      cfa.take(js, cs, d, n, fits)
    case CF.PassRecover{js, cs}:
      cfa.recover(js, cs, fits)
    case CF.PassFinish{js, cs, r, b, n}:
      cfa.finish(js, cs, r, b, n, fits)
