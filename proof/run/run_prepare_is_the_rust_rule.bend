# eukhe: the proof of LAW run_prepare_is_the_rust_rule

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run.bend as Run

def rk.run_prepare_is_the_rust_rule(+compacted: Bool, +th: RnDecision.Th) -> {RnDecision.decide.prepare(compacted, th) == Run.rust.before_request(compacted, th) : RnDecision.Prepared}:
  match compacted th:
    case True{} RnDecision.Under{}:
      {==}
    case True{} RnDecision.Background{}:
      {==}
    case True{} RnDecision.Blocking{}:
      {==}
    case False{} RnDecision.Under{}:
      {==}
    case False{} RnDecision.Background{}:
      {==}
    case False{} RnDecision.Blocking{}:
      {==}

def Run.run_prepare_is_the_rust_rule(compacted, th):
  rk.run_prepare_is_the_rust_rule(compacted, th)
