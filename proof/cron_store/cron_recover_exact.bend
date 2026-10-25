# eukhe: the proof of LAW cron_recover_exact
# A case split on the status, the schedule and whether a claim was cleared.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def cx.recover(f: CS.Fact, c: Bool) -> {CS.recover(f, c) == CronStore.recover_spec(f, c) : CS.Back}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st p:
        case Cr.Active{} CS.POnce{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Active{} CS.PEvery{ms}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Active{} CS.PRule{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Paused{} _:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Finished{} _:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Cancelled{} _:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}

# the model's pause in minutes is the spec's table

def CronStore.cron_recover_exact(f, c):
  cx.recover(f, c)
