# eukhe: the proof of LAW cron_once_refires
# The model's verdict Cr.clears is the spec's clears_spec
# (LCj.cj.clears), so the claim is cleared; an
# active one-shot's recovery then computes.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob
import ./base.bend as LCj

def CronJob.cron_once_refires(p, dead, i, d, nx, k, oc, o, rs, ss, h, cl):
  +eq = Equal.trans(Bool, Cr.clears(p, o, rs, dead), CronJob.clears_spec(p, o, rs, dead), True{}, LCj.cj.clears(p, o, rs, dead), cl)
  %Equal.sym(Bool, Cr.clears(p, o, rs, dead), True{}, eq) : {Cr.recover.go(_, i, Cr.Once{d}, Cr.Active{}, nx, k, Cr.Claim{oc, o}, rs, ss, h) == Cr.Job{i, Cr.Once{d}, Cr.Active{}, Some{oc}, k, None{}, rs, Nil{}, h} : Cr.Job}
  {==}
