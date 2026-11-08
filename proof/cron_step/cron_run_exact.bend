# eukhe: the proof of LAW cron_run_exact
# By induction on the events: each event's step is the spec's
# (cron_step_exact); Cr.run is Cr.go from the empty file.

import Base
import ../../bend/cron.bend as Cr
import ./cron_step_exact.bend as PX0
import ../../laws/cron_step.bend as CronStep

def cr.go(evs: List<&2, Cr.Ev>, +s: Cr.S) -> {Cr.go(evs, s) == CronStep.run_from_spec(evs, s) : Cr.S}:
  match evs:
    case Nil{}:
      {==}
    case +e <> rest:
      %CronStep.cron_step_exact(s, e) : {Cr.go(rest, Cr.step(s, e)) == CronStep.run_from_spec(rest, _) : Cr.S}
      cr.go(rest, Cr.step(s, e))

# CronStep

def CronStep.cron_run_exact(evs, s):
  (cr.go(evs, s), cr.go(evs, Cr.S.empty()))
