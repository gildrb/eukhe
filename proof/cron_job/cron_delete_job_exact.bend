# eukhe: the proof of LAW cron_delete_job_exact
# Both sides build the same job.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob

def CronJob.cron_delete_job_exact(j):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}
