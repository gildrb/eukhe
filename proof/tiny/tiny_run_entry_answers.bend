# eukhe: the proof of LAW tiny_run_entry_answers
#
# PROOF: the spelled outcome reads back whole with nothing left
# (tre.seen), so the entry steps the model's run (Tn.step_run) and spells
# its reply as sp_w_do does (tre.reply).

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_run.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/tiny/run.bend as TinyRun
import ./base/run_entry.bend as LTre

def TinyRun.tiny_run_entry_answers(x, e, h):
  %Equal.sym(Wr.Dec<Tn.Seen>, FTr.get_seen(TinyRun.sp_w_seen(e, "")), Wr.Got{e, ""}, LTre.tre.seen(e, "", h)) : {FTr.step.got(x, _) == TinyRun.sp_reply(Tn.step_run(x, e)) : FTr.St & String}
  LTre.tre.reply(Tn.step_run(x, e))
