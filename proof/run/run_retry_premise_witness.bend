# eukhe: the proof of LAW run_retry_premise_witness

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def Laws.run_retry_premise_witness():
  (Rn.At{1n, 0n, 0n, False{}}, {==})
