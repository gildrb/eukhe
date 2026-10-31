# eukhe: the proof of LAW cron_halt_exact
# A case split on the hold, then on the status.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def cx.halt_st(h: CS.Halt, st: Cr.Status, p: CS.Plan, nx: Maybe<&2, Nat>, k: Nat) -> {CS.halt(CS.Fact{st, p, nx, k}, h) == CronStore.halt_spec(CS.Fact{st, p, nx, k}, h) : CS.Cut}:
  match h:
    case CS.HPause{}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}
    case CS.HStop{}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}
    case CS.HDelete{}:
      {==}

def CronStore.cron_halt_exact(f, h):
  match f:
    case CS.Fact{st, p, nx, k}:
      cx.halt_st(h, st, p, nx, k)
