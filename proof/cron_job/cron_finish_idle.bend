# eukhe: the proof of LAW cron_finish_idle
# The premise takes the model's finish step through the arm of a job p
# does not run (Cr.finish.run), which builds the job again.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron.bend as Cron
import ../../laws/cron_job.bend as CronJob

def CronJob.cron_finish_idle(p, c, o, j, idle):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      %Equal.sym(Bool, Cr.has(p, rs), False{}, idle) : {Cr.finish.run(_, p, c, o, i, s, st, nx, k, cl, rs, ss, h) == Cr.Job{i, s, st, nx, k, cl, rs, ss, h} : Cr.Job}
      {==}
