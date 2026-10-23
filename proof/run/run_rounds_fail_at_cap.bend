# eukhe: the proof of LAW run_rounds_fail_at_cap

import Base
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ./base.bend as LA

# a run the cap failed made max(cap, 1) rounds
def caps_of(+cfg: RnState.Cfg, +s: RnState.St, +k: Nat, i: LA.InvS(cfg, s, k)) -> Or({RnState.capped(s) == False{} : Bool}, {k == Nat.max(RnState.Cfg.cap(cfg), 1n) : Nat}):
  (cp, co) = i
  cp

def rounds_fail_at_cap(+cfg: RnState.Cfg, +evs: List<&2, RnState.Ev>) -> Or({RnState.capped(RnStep.run(cfg, evs)) == False{} : Bool}, {RnMeasure.rounds(cfg, evs) == Nat.max(RnState.Cfg.cap(cfg), 1n) : Nat}):
  caps_of(cfg, RnStep.run(cfg, evs), RnMeasure.rounds(cfg, evs), LA.inv_run(evs, cfg, RnState.init(cfg), 0n, LA.inv_init(cfg)))

def Run.run_rounds_fail_at_cap(cfg, evs):
  rounds_fail_at_cap(cfg, evs)
