# eukhe: the proof of LAW config_ffi_total
# The entry reads every input as the laws' reader does (LFR.pfc.ask); a
# request read whole is answered as the laws spell its decision
# (LFP.pfr.answer); anything else is the error form.

import Base
import ../../bend/ffi_config.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/config.bend as Config
import ../../spec/settings/config.bend as CS
import ./base/ffi_read.bend as LFR
import ./base/ffi_reply.bend as LFP

def pto.end(b: Bool, a: FC.Ask) -> {FC.run.end(b, a) == Config.cf_entry.of(CS.cf_r_end(b, a)) : String}:
  match b:
    case True{}:
      LFP.pfr.answer(a)
    case False{}:
      {==}

def pto.whole(r: Wr.Dec<FC.Ask>) -> {FC.run(r) == Config.cf_entry.of(CS.cf_r_whole(r)) : String}:
  match r:
    case Wr.Got{a, s}:
      pto.end(Wr.end(s), a)
    case Wr.Bad{}:
      {==}

def Config.config_ffi_total(s):
  %Equal.sym(Wr.Dec<FC.Ask>, FC.get_ask(Wr.get_nat(s)), CS.cf_r_ask(Wr.get_nat(s)), LFR.pfc.ask(Wr.get_nat(s))) : {FC.run(_) == Config.cf_entry(s) : String}
  pto.whole(CS.cf_r_ask(Wr.get_nat(s)))
