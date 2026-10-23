# eukhe: the proof of LAW run_prepare_compacted_reads_no_threshold

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run.bend as Run

def rk.run_prepare_compacted_reads_no_threshold(+th: RnDecision.Th) -> {RnDecision.decide.prepare(True{}, th) == RnDecision.decide.prepare(True{}, RnDecision.Under{}) : RnDecision.Prepared}:
  match th:
    case RnDecision.Under{}:
      {==}
    case RnDecision.Background{}:
      {==}
    case RnDecision.Blocking{}:
      {==}

def Run.run_prepare_compacted_reads_no_threshold(th):
  rk.run_prepare_compacted_reads_no_threshold(th)
