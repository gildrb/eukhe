# eukhe: the proof of LAW run_note_spends_no_retry

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

# a noted error spends a note, retryable or not, and keeps the retries
def note_spends_no_retry(+cfg: Rn.Cfg, -retryable: Bool, +r: Nat, +c: Nat, +a: Nat, +m: Nat, +p: Nat) -> {Rn.call(cfg, Rn.Error{retryable, True{}}, r, c, a, 1n+m, p) == Rn.St{Rn.Prepare{}, r, c, a, m, Rn.Cfg.polls(cfg)} : Rn.St}:
  {==}

def Laws.run_note_spends_no_retry(cfg, retryable, r, c, a, m, p):
  note_spends_no_retry(cfg, retryable, r, c, a, m, p)
