# eukhe: the proof of LAW cron_pause_job_exact
# By cases on the job's status: each side builds the same job.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob

def CronJob.cron_pause_job_exact(j):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}
