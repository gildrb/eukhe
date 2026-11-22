# eukhe: the proof of LAW run_steps_exact
#
# PROOF: the reply and the round's end are run_step_exact's lemmas
# (rmx.call, rmx.tools); a noted reply and an error that is no cut
# compute case by case.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/machine.bend as RunMachine
import ./run_step_exact.bend as PRunStepExact

def sx.note(cfg: RnState.Cfg, -retryable: Bool, -r: Nat, -c: Nat, -a: Nat, n: Nat, -p: Nat) -> {RnStep.note(cfg, r, c, a, n, p) == RunMachine.rm.error(cfg, True{}, retryable, r, c, a, n, p) : RnState.St}:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          {==}

def sx.retry(cfg: RnState.Cfg, retryable: Bool, -r: Nat, -c: Nat, a: Nat, -n: Nat, -p: Nat) -> {RnStep.retry(cfg, retryable, r, c, a, n, p) == RunMachine.rm.error(cfg, False{}, retryable, r, c, a, n, p) : RnState.St}:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      match retryable a:
        case True{} 1n+b:
          {==}
        case True{} 0n:
          {==}
        case False{} a:
          {==}

def RunMachine.run_steps_exact(cfg, reply, fin, retryable, r, c, a, n, p):
  (PRunStepExact.rmx.call(cfg, reply, r, c, a, n, p), (PRunStepExact.rmx.tools(cfg, fin, r, c, a, n, p), (sx.note(cfg, retryable, r, c, a, n, p), sx.retry(cfg, retryable, r, c, a, n, p))))
