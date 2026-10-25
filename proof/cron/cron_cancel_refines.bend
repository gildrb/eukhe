# eukhe: the proof of LAW cron_cancel_refines
# A case split on the job's status: both sides compute.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron.bend as Cron

def Cron.cron_cancel_refines(v, j):
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
