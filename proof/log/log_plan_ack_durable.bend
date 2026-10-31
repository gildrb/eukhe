# eukhe: the proof of LAW log_plan_ack_durable
#
# The plan's epoch is the model's (log_plan_runs_the_model), whose
# acknowledged commits a crash keeps (log_ack_durable).

import Base
import ../../spec/durable/log.bend as Lg
import ../../laws/log.bend as Log
import ./log_ack_durable.bend as PAck
import ./log_plan_runs_the_model.bend as PRun

def Log.log_plan_ack_durable(d, e):
  match e:
    case Lg.Epoch{+cs, +p, +k, +drop}:
      +x = Log.log_exec(Log.log_epoch_plan(cs), p, Lg.open(d))
      %Equal.sym(Lg.St, x, Lg.run(d, cs, p), Log.log_plan_runs_the_model(d, cs, p)) : &r: List<&2, List<&2, Nat>> -> {Lg.Disk.log(Lg.crash(k, drop, _)) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Lg.St.acked(_)), r) : List<&2, List<&2, Nat>>}
      Log.log_ack_durable(d, Lg.Epoch{cs, p, k, drop})
