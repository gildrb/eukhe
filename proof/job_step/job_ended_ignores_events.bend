# eukhe: the proof of LAW job_ended_ignores_events
# Induction on the events: the entry answers an ended job with itself and
# no end.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ./base.bend as LA

def JobStep.job_ended_ignores_events(t, cap, k, d, x, es):
  (Equal.sym(Jb.J, Jb.Ended{k, d, x}, JobStep.fed(es, t, cap, Jb.Ended{k, d, x}), LA.js.fed_ended(es, t, cap, k, d, x)), Equal.sym(List<&2, Jb.End>, Nil{}, JobStep.fed_ends(es, t, cap, Jb.Ended{k, d, x}), LA.js.fed_ends_ended(es, t, cap, k, d, x)))
