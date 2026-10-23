# eukhe: the proof of LAW run_counts_within_witness

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def Laws.run_counts_within_witness():
  (Rn.Lim{1n, 0n, 0n, 0n}, (Rn.At{1n, 0n, 0n, False{}}, {==}))
