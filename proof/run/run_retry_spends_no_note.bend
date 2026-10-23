# eukhe: the proof of LAW run_retry_spends_no_note

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run

# a retryable error that is not noted spends a retry and keeps the notes
def retry_spends_no_note(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +b: Nat, +n: Nat, +p: Nat) -> {RnStep.call(cfg, RnState.Error{True{}, False{}}, r, c, 1n+b, n, p) == RnState.St{RnState.Prepare{}, r, c, b, n, RnState.Cfg.polls(cfg)} : RnState.St}:
  {==}

def Run.run_retry_spends_no_note(cfg, r, c, b, n, p):
  retry_spends_no_note(cfg, r, c, b, n, p)
