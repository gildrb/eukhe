# eukhe: the proof of LAW facts_cache_write_1h_exact

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts

def pf.facts_cache_write_1h_exact(row: Maybe<&2, Nat>, +input: Nat, +write: Nat) -> {Fx.rate_1h(row, input, write) == Facts.rate_1h_spec(row, input, write) : Nat}:
  match row:
    case Some{k}:
      {==}
    case None{}:
      {==}

def Facts.facts_cache_write_1h_exact(row, input, write):
  pf.facts_cache_write_1h_exact(row, input, write)
