# eukhe: the proof of LAW run_prepare_compacted_reads_no_threshold

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def rk.run_prepare_compacted_reads_no_threshold(+th: Rn.Th) -> {Rn.decide.prepare(True{}, th) == Rn.decide.prepare(True{}, Rn.Under{}) : Rn.Prepared}:
  match th:
    case Rn.Under{}:
      {==}
    case Rn.Background{}:
      {==}
    case Rn.Blocking{}:
      {==}

def Run.run_prepare_compacted_reads_no_threshold(th):
  rk.run_prepare_compacted_reads_no_threshold(th)
