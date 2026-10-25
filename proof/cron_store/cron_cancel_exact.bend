# eukhe: the proof of LAW cron_cancel_exact
# A case split on the status.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def cx.cancel(f: CS.Fact) -> {CS.cancel(f) == CronStore.cancel_spec(f) : CS.Cut}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def CronStore.cron_cancel_exact(f):
  cx.cancel(f)
