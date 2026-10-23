# eukhe: the proof of LAW run_compact_is_the_rust_rule

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def rk.run_compact_is_the_rust_rule(+over: Bool, +got: Rn.Got) -> {Rn.decide.compact(over, got) == Run.rust.after_compaction(over, got) : Bool}:
  match over got:
    case True{} Rn.Built{}:
      {==}
    case True{} Rn.Kept{}:
      {==}
    case True{} Rn.Broke{}:
      {==}
    case False{} Rn.Built{}:
      {==}
    case False{} Rn.Kept{}:
      {==}
    case False{} Rn.Broke{}:
      {==}

def Run.run_compact_is_the_rust_rule(over, got):
  rk.run_compact_is_the_rust_rule(over, got)
