# eukhe: the proof of LAW tiny_run_entry_answers
#
# PROOF: the spelled outcome reads back whole with nothing left
# (tre.seen), so the entry steps the model's run (Tn.step_run), which is
# the spec's table (tiny_run_step_is_model), and spells the reply as the
# spec does (tre.reply).

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_run.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/tiny/run.bend as TinyRun
import ./tiny_run_step_is_model.bend as PTinyRunStepIsModel
import ./base/run_entry.bend as LTre

# the entry's step of a run is the spec's
def tra.step(x: Tn.Run, +e: Tn.Seen) -> {FTr.reply(Tn.step_run(x, e)) == TinyRun.sp_reply(TinyRun.sp_step_r(x, e)) : FTr.St & String}:
  match x:
    case Tn.Run{+m, +ph}:
      %TinyRun.tiny_run_step_is_model(m, ph, e) : {FTr.reply(Tn.step_run(Tn.Run{m, ph}, e)) == TinyRun.sp_reply(_) : FTr.St & String}
      LTre.tre.reply(Tn.step_run(Tn.Run{m, ph}, e))

def TinyRun.tiny_run_entry_answers(x, e, h):
  %Equal.sym(Wr.Dec<Tn.Seen>, FTr.get_seen(TinyRun.sp_w_seen(e, "")), Wr.Got{e, ""}, LTre.tre.seen(e, "", h)) : {FTr.step.got(x, _) == TinyRun.sp_reply(TinyRun.sp_step_r(x, e)) : FTr.St & String}
  tra.step(x, e)
