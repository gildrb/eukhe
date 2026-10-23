# eukhe: the proof of LAW run_retry_premise_witness

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run.bend as Run

def Run.run_retry_premise_witness():
  (RnDecision.At{1n, 0n, 0n, False{}}, {==})
