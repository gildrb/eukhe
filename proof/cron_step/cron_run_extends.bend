# eukhe: the proof of LAW cron_run_extends
# Cr.run is the fold Cr.go from the empty file. The fold over events
# followed by one more event e is the step of e after the fold, from any
# state (crx.snoc, by induction on the events).

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_step.bend as CronStep

def crx.snoc(evs: List<&2, Cr.Ev>, +s: Cr.S, +e: Cr.Ev) -> {Cr.go(List.append(&2, Cr.Ev, evs, [e]), s) == Cr.step(Cr.go(evs, s), e) : Cr.S}:
  match evs:
    case Nil{}:
      {==}
    case +h <> t:
      crx.snoc(t, Cr.step(s, h), e)

# CronStep

def CronStep.cron_run_extends(evs, e):
  ({==}, crx.snoc(evs, Cr.S.empty(), e))
