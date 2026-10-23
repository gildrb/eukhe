# eukhe: the proof of LAW run_retry_premise_witness

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def Run.run_retry_premise_witness():
  (Rn.At{1n, 0n, 0n, False{}}, {==})
