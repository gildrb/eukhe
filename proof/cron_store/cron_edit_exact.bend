# eukhe: the proof of LAW cron_edit_exact
# A case split on the status, then on the new first run.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def CronStore.cron_edit_exact(f, at):
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          match at:
            case None{}:
              {==}
            case Some{a}:
              {==}
        case Cr.Paused{}:
          match at:
            case None{}:
              {==}
            case Some{a}:
              {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}
