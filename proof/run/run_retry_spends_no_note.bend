# eukhe: the proof of LAW run_retry_spends_no_note

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

# a retryable error that is not noted spends a retry and keeps the notes
def retry_spends_no_note(+cfg: Rn.Cfg, +r: Nat, +c: Nat, +b: Nat, +n: Nat, +p: Nat) -> {Rn.call(cfg, Rn.Error{True{}, False{}}, r, c, 1n+b, n, p) == Rn.St{Rn.Prepare{}, r, c, b, n, Rn.Cfg.polls(cfg)} : Rn.St}:
  {==}

def Run.run_retry_spends_no_note(cfg, r, c, b, n, p):
  retry_spends_no_note(cfg, r, c, b, n, p)
