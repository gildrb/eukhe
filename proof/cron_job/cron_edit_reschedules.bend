# eukhe: the proof of LAW cron_edit_reschedules
# A case split on the status: the model gives an active or a paused job
# the schedule, the jobs the store's edit answers Edited.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_job.bend as CronJob

def CronJob.cron_edit_reschedules(v, c, k, j):
  match j:
    case Cr.Job{i, s, st, nx, kk, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}
