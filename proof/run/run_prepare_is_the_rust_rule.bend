# eukhe: the proof of LAW run_prepare_is_the_rust_rule

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def rk.run_prepare_is_the_rust_rule(+compacted: Bool, +th: Rn.Th) -> {Rn.decide.prepare(compacted, th) == Run.rust.before_request(compacted, th) : Rn.Prepared}:
  match compacted th:
    case True{} Rn.Under{}:
      {==}
    case True{} Rn.Background{}:
      {==}
    case True{} Rn.Blocking{}:
      {==}
    case False{} Rn.Under{}:
      {==}
    case False{} Rn.Background{}:
      {==}
    case False{} Rn.Blocking{}:
      {==}

def Run.run_prepare_is_the_rust_rule(compacted, th):
  rk.run_prepare_is_the_rust_rule(compacted, th)
