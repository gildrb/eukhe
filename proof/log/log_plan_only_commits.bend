# eukhe: the proof of LAW log_plan_only_commits
#
# The plan's epoch is the model's (log_plan_runs_the_model), after which
# the log holds a prefix of the commits (log_only_commits).

import Base
import ../../spec/log.bend as Lg
import ../../laws/log.bend as Log
import ./log_only_commits.bend as POnly
import ./log_plan_runs_the_model.bend as PRun

def Log.log_plan_only_commits(d, e):
  match e:
    case Lg.Epoch{+cs, +p, +k, +drop}:
      +x = Log.log_exec(Log.log_epoch_plan(cs), p, Lg.open(d))
      %Equal.sym(Lg.St, x, Lg.run(d, cs, p), Log.log_plan_runs_the_model(d, cs, p)) : &n: Nat -> {Lg.Disk.log(Lg.crash(k, drop, _)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), List.take(&2, List<&2, Nat>, cs, n)) : List<&2, List<&2, Nat>>}
      Log.log_only_commits(d, Lg.Epoch{cs, p, k, drop})
