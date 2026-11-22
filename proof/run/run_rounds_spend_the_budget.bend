# eukhe: the proof of LAW run_rounds_spend_the_budget
#
# PROOF: the round invariant of the run area (base.bend, InvS, by
# induction on the inputs) says it: a run that did not fail made
# cap - 1 - r rounds.

import Base
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run
import ./base.bend as LA

# a run that did not fail made max(cap, 1) - 1 - r rounds
def rb.of(+cfg: RnState.Cfg, +s: RnState.St, +k: Nat, i: LA.InvS(cfg, s, k)) -> Or({RnState.failed(s) == True{} : Bool}, {Nat.add(k, 1n+RnState.St.r(s)) == Nat.max(RnState.Cfg.cap(cfg), 1n) : Nat}):
  (cp, co) = i
  co

def Run.run_rounds_spend_the_budget(cfg, evs):
  rb.of(cfg, RnStep.run(cfg, evs), RnMeasure.rounds(cfg, evs), LA.inv_run(evs, cfg, RnState.init(cfg), 0n, LA.inv_init(cfg)))
