# eukhe: the proof of LAW cron_resume_job_exact
# By cases on the schedule, then on the status of an interval.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob

def CronJob.cron_resume_job_exact(c, j):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          {==}
        case Cr.Every{n}:
          match st:
            case Cr.Active{}:
              {==}
            case Cr.Paused{}:
              {==}
            case Cr.Finished{}:
              {==}
            case Cr.Cancelled{}:
              {==}
