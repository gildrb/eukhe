# eukhe: the proof of LAW job_exit_ends_exited
# The exit ends the live job with its code and counts; from then on the
# job is ended (js.fed_ended, js.fed_ends_ended).

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ./base.bend as LA

def JobStep.job_exit_ends_exited(t, cap, k, d, c, es):
  +e1 = Equal.sym(Jb.J, Jb.Ended{k, d, Jb.Exited{c}}, JobStep.fed(es, t, cap, Jb.Ended{k, d, Jb.Exited{c}}), LA.js.fed_ended(es, t, cap, k, d, Jb.Exited{c}))
  +F = JobStep.fed_ends(es, t, cap, Jb.Ended{k, d, Jb.Exited{c}})
  +e2 = Equal.cong(List<&2, Jb.End>, List<&2, Jb.End>, z => List.append(&2, Jb.End, [Jb.Exited{c}], z), F, Nil{}, Equal.sym(List<&2, Jb.End>, Nil{}, F, LA.js.fed_ends_ended(es, t, cap, k, d, Jb.Exited{c})))
  (e1, e2)
