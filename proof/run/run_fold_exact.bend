# eukhe: the proof of LAW run_fold_exact
#
# PROOF: induction on the inputs, from any state; each step is
# run_step_exact (rmx.step). Both runs start from the same state.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/machine.bend as RunMachine
import ./run_step_exact.bend as PRunStepExact

def rfx.go(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St) -> {RnStep.run.go(evs, cfg, s) == RunMachine.rm.run.go(evs, cfg, s) : RnState.St}:
  match evs:
    case Nil{}:
      {==}
    case +e <> rest:
      %PRunStepExact.rmx.step(cfg, s, e) : {RnStep.run.go(rest, cfg, RnStep.step(cfg, s, e)) == RunMachine.rm.run.go(rest, cfg, _) : RnState.St}
      rfx.go(rest, cfg, RnStep.step(cfg, s, e))

def RunMachine.run_fold_exact(cfg, evs):
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      rfx.go(evs, RnState.Cfg{cap, polls, retries, notes}, RnState.St{RnState.Prepare{}, Nat.sub(cap, 1n), 1n, retries, notes, polls})
