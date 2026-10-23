# eukhe: the proof of LAW run_compact_is_the_rust_rule

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run.bend as Run

def rk.run_compact_is_the_rust_rule(+over: Bool, +got: RnState.Got) -> {RnDecision.decide.compact(over, got) == Run.rust.after_compaction(over, got) : Bool}:
  match over got:
    case True{} RnState.Built{}:
      {==}
    case True{} RnState.Kept{}:
      {==}
    case True{} RnState.Broke{}:
      {==}
    case False{} RnState.Built{}:
      {==}
    case False{} RnState.Kept{}:
      {==}
    case False{} RnState.Broke{}:
      {==}

def Run.run_compact_is_the_rust_rule(over, got):
  rk.run_compact_is_the_rust_rule(over, got)
