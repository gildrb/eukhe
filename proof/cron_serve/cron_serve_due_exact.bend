# eukhe: the proof of LAW cron_serve_due_exact
# The claim pass is the spec's (cron_take_exact); its answer is read the
# same way on both sides (a case split).

import Base
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_serve/serve.bend as CronServe
import ../cron_store/cron_take_exact.bend as PX0

def sd.took(t: CS.Took) -> {Sv.due.took(t) == CronServe.sv_due.took(t) : Bool}:
  match t:
    case CS.Keep{}:
      {==}
    case CS.Roll{n}:
      {==}
    case CS.Claimed{n}:
      {==}

def CronServe.cron_serve_due_exact(f, now):
  %CronStore.cron_take_exact(f, False{}, now, now) : {Sv.due.took(CS.take(f, False{}, now, now)) == CronServe.sv_due.took(_) : Bool}
  sd.took(CS.take(f, False{}, now, now))
