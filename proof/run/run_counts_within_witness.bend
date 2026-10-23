# eukhe: the proof of LAW run_counts_within_witness

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run.bend as Run

def Run.run_counts_within_witness():
  (RnDecision.Lim{1n, 0n, 0n, 0n}, (RnDecision.At{1n, 0n, 0n, False{}}, {==}))
