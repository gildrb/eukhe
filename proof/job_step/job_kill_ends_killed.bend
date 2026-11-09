# eukhe: the proof of LAW job_kill_ends_killed
# The kill ends the live job with its counts; from then on the job is
# ended (js.fed_ended, js.fed_ends_ended).

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ./base.bend as LA

def JobStep.job_kill_ends_killed(t, cap, k, d, es):
  +e1 = Equal.sym(Jb.J, Jb.Ended{k, d, Jb.Killed{}}, JobStep.fed(es, t, cap, Jb.Ended{k, d, Jb.Killed{}}), LA.js.fed_ended(es, t, cap, k, d, Jb.Killed{}))
  +F = JobStep.fed_ends(es, t, cap, Jb.Ended{k, d, Jb.Killed{}})
  +e2 = Equal.cong(List<&2, Jb.End>, List<&2, Jb.End>, z => List.append(&2, Jb.End, [Jb.Killed{}], z), F, Nil{}, Equal.sym(List<&2, Jb.End>, Nil{}, F, LA.js.fed_ends_ended(es, t, cap, k, d, Jb.Killed{})))
  (e1, e2)
