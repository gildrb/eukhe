# eukhe: the proof of LAW cron_entry_malformed_exact
# The entry reads every input as the laws' reader does (LCe.cre.ask); where
# that reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/cron_store.bend as CS
import ../../bend/ffi_cron.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/cron.bend as Cron
import ./base/entry.bend as LCe

def crm.end(b: Bool, -a: CS.Ask, no: {Cron.read_ask.end(b, a) == None{} : Maybe<&2, CS.Ask>}) -> {FC.run.end(b, a) == SCon{'E', SCon{' ', "cron: malformed request"}} : String}:
  match b:
    case True{}:
      LCe.cre.some_none(CS.Ask, a, {FC.answer(a) == SCon{'E', SCon{' ', "cron: malformed request"}} : String}, no)
    case False{}:
      {==}

def crm.whole(r: Wr.Dec<CS.Ask>, no: {Cron.read_ask.whole(r) == None{} : Maybe<&2, CS.Ask>}) -> {FC.run(r) == SCon{'E', SCon{' ', "cron: malformed request"}} : String}:
  match r:
    case Wr.Got{a, s}:
      crm.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def Cron.cron_entry_malformed_exact(s, no):
  %LCe.cre.ask(Wr.get_nat(s)) : {FC.run(_) == SCon{'E', SCon{' ', "cron: malformed request"}} : String}
  crm.whole(Cron.read_ask.go(Wr.get_nat(s)), no)
