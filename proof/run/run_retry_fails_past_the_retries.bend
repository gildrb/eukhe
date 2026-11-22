# eukhe: the proof of LAW run_retry_fails_past_the_retries
#
# PROOF: RnStep.retry computes on the retryable flag and the retries left;
# an error that is not noted reaches RnStep.retry through RnStep.error.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run

# a retryable error with a retry left is prepared again with one retry fewer
def rf.more(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +b: Nat, +n: Nat, +p: Nat) -> {RnStep.retry(cfg, True{}, r, c, 1n+b, n, p) == RnState.St{RnState.Prepare{}, r, c, b, n, RnState.Cfg.polls(cfg)} : RnState.St}:
  {==}

# a retryable error with no retry left fails the run on the model
def rf.none(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +n: Nat, +p: Nat) -> {RnStep.retry(cfg, True{}, r, c, 0n, n, p) == RnState.St{RnState.Failed{RnState.Model{}}, r, c, 0n, n, p} : RnState.St}:
  {==}

# an error that is not retryable fails the run on the model
def rf.fatal(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {RnStep.retry(cfg, False{}, r, c, a, n, p) == RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p} : RnState.St}:
  {==}

# a retryable error that is not noted, past the retries, fails the run on the model
def rf.call(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +n: Nat, +p: Nat) -> {RnStep.call(cfg, RnState.Error{True{}, False{}}, r, c, 0n, n, p) == RnState.St{RnState.Failed{RnState.Model{}}, r, c, 0n, n, p} : RnState.St}:
  {==}

def Run.run_retry_fails_past_the_retries(cfg, r, c, a, b, n, p):
  (rf.more(cfg, r, c, b, n, p), (rf.none(cfg, r, c, n, p), (rf.fatal(cfg, r, c, a, n, p), rf.call(cfg, r, c, n, p))))
