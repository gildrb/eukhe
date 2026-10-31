# eukhe: the proof of LAW config_ffi_answers
# The entry reads as the laws' reader (LFR.pfc.ask), which reads a spelled
# request back whole (LFS.pfs.ask_rt); the entry then writes the model's
# decision as the laws spell it (LFP.pfr.answer).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../bend/ffi_config.bend as FC
import ../../bend/wire.bend as Wr
import ../../spec/settings/config.bend as CS
import ./base/ffi_read.bend as LFR
import ./base/ffi_spell.bend as LFS
import ./base/ffi_reply.bend as LFP

def Config.config_ffi_answers(a, fits):
  %Equal.sym(Wr.Dec<FC.Ask>, FC.get_ask(Wr.get_nat(CS.cf_w_ask(a))), CS.cf_r_ask(Wr.get_nat(CS.cf_w_ask(a))), LFR.pfc.ask(Wr.get_nat(CS.cf_w_ask(a)))) : {FC.run(_) == CS.cf_w_reply(a) : String}
  %LFS.pfs.ask_rt(a, fits) : {FC.run(_) == CS.cf_w_reply(a) : String}
  LFP.pfr.answer(a)
