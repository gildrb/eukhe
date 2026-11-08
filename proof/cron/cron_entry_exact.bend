# eukhe: the proof of LAW cron_entry_exact
# The entry reads every input as the laws' reader does (LCe.cre.ask); a
# whole request gets the entry's answer, which is the laws' reply
# (LAn.cran.answer: each decision is its spec, and the entry's writers
# write the laws' spelling); anything else gets the error form.

import Base
import ../../bend/cron_store.bend as CS
import ../../bend/ffi_cron.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/cron.bend as Cron
import ./base/answer.bend as LAn
import ./base/entry.bend as LCe

def cex.end(b: Bool, a: CS.Ask) -> {FC.run.end(b, a) == Cron.entry_spec.go(Cron.read_ask.end(b, a)) : String}:
  match b:
    case True{}:
      LAn.cran.answer(a)
    case False{}:
      {==}

def cex.whole(r: Wr.Dec<CS.Ask>) -> {FC.run(r) == Cron.entry_spec.go(Cron.read_ask.whole(r)) : String}:
  match r:
    case Wr.Got{a, s}:
      cex.end(Wr.end(s), a)
    case Wr.Bad{}:
      {==}

def Cron.cron_entry_exact(s):
  %LCe.cre.ask(Wr.get_nat(s)) : {FC.run(_) == Cron.entry_spec(s) : String}
  cex.whole(Cron.read_ask.go(Wr.get_nat(s)))
