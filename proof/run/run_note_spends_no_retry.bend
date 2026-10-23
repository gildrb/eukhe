# eukhe: the proof of LAW run_note_spends_no_retry

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run

# a noted error spends a note, retryable or not, and keeps the retries
def note_spends_no_retry(+cfg: RnState.Cfg, -retryable: Bool, +r: Nat, +c: Nat, +a: Nat, +m: Nat, +p: Nat) -> {RnStep.call(cfg, RnState.Error{retryable, True{}}, r, c, a, 1n+m, p) == RnState.St{RnState.Prepare{}, r, c, a, m, RnState.Cfg.polls(cfg)} : RnState.St}:
  {==}

def Run.run_note_spends_no_retry(cfg, retryable, r, c, a, m, p):
  note_spends_no_retry(cfg, retryable, r, c, a, m, p)
