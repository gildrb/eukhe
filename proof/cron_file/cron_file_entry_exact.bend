# eukhe: the proof of LAW cron_file_entry_exact
# The entry reads every input as the laws' reader does (LCfw.cfe.pass); a
# whole request gets the entry's answer, which is the laws' reply (each
# pass being its spec: the cron_file_*_exact laws; the entry's writers
# write the laws' spelling); anything else gets the error form.
import Base
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../bend/ffi_cron_file.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/cron.bend as Cron
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ./base/wire.bend as LCfw
import ./cron_file_take_exact.bend as PTake
import ./cron_file_recover_exact.bend as PRecover
import ./cron_file_finish_exact.bend as PFinish

# the entry's answer to every request is the laws' reply to it
def cfx.answer(a: CF.Pass) -> {FF.answer(a) == CronFileEntry.spell_answer(a) : String}:
  match a:
    case CF.PassTake{+js, +cs, +d, +n}:
      %CronFile.cron_file_take_exact(js, cs, d, n) : {FF.put_tooks(CF.take(js, cs, d, n), "") == Wr.put_list(~CS.Took, ~Cron.spell_took, _, "") : String}
      LCfw.cfw.tooks(CF.take(js, cs, d, n), "")
    case CF.PassRecover{+js, +cs}:
      %CronFile.cron_file_recover_exact(js, cs) : {FF.put_swept(CF.recover(js, cs), "") == CronFileEntry.spell_swept(_) : String}
      %LCfw.cfw.backs(CF.recover.js(js, cs), "") : {FF.put_swept(CF.recover(js, cs), "") == CronFileEntry.spell_keeps(CF.keeps(cs), _) : String}
      {==}
    case CF.PassFinish{+js, +cs, +r, +bb, +n}:
      %CronFile.cron_file_finish_exact(60000n, js, cs, r, bb, n) : {FF.put_closed(CF.finish(60000n, js, cs, r, bb, n), "") == CronFileEntry.spell_closed(_) : String}
      %LCfw.cfw.fins(CF.finish.js(js, CF.hit(cs), 60000n, r, bb, n), "") : {FF.put_closed(CF.finish(60000n, js, cs, r, bb, n), "") == CronFileEntry.spell_keeps(CF.drops(cs, False{}), _) : String}
      {==}

def cfx.end(b: Bool, a: CF.Pass) -> {FF.run.end(b, a) == CronFileEntry.entry_spec.go(CronFileEntry.read_pass.end(b, a)) : String}:
  match b:
    case True{}:
      cfx.answer(a)
    case False{}:
      {==}

def cfx.whole(r: Wr.Dec<CF.Pass>) -> {FF.run(r) == CronFileEntry.entry_spec.go(CronFileEntry.read_pass.whole(r)) : String}:
  match r:
    case Wr.Got{a, s}:
      cfx.end(Wr.end(s), a)
    case Wr.Bad{}:
      {==}

def CronFileEntry.cron_file_entry_exact(s):
  %LCfw.cfe.pass(Wr.get_nat(s)) : {FF.run(_) == CronFileEntry.entry_spec(s) : String}
  cfx.whole(CronFileEntry.read_pass.go(Wr.get_nat(s)))
