# eukhe: the proof of LAW run_prepare_follows_the_thresholds
#
# PROOF: by computation on the generation and the threshold.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/model.bend as Run

def prep.under(+compacted: Bool) -> {RnDecision.decide.prepare(compacted, RnDecision.Under{}) == RnDecision.Sends{False{}} : RnDecision.Prepared}:
  match compacted:
    case True{}:
      {==}
    case False{}:
      {==}

def prep.compacted(+th: RnDecision.Th) -> {RnDecision.decide.prepare(True{}, th) == RnDecision.Sends{False{}} : RnDecision.Prepared}:
  match th:
    case RnDecision.Under{}:
      {==}
    case RnDecision.Background{}:
      {==}
    case RnDecision.Blocking{}:
      {==}

def Run.run_prepare_follows_the_thresholds(compacted, th):
  (prep.under(compacted), prep.compacted(th), {==}, {==})
