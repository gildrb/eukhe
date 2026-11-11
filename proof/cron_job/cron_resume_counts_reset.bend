# eukhe: the proof of LAW cron_resume_counts_reset
# A case split on the schedule and the status: the model counts a reset
# exactly for an active or paused interval, the jobs the store's resume
# answers Resumed.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_job.bend as CronJob

def CronJob.cron_resume_counts_reset(v, c, j):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          match st:
            case Cr.Active{}:
              {==}
            case Cr.Paused{}:
              {==}
            case Cr.Finished{}:
              {==}
            case Cr.Cancelled{}:
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
