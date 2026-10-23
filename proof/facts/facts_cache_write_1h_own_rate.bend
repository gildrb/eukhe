# eukhe: the proof of LAW facts_cache_write_1h_own_rate

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def pf.facts_cache_write_1h_own_rate(+input: Nat, +write: Nat) -> {Fx.rate_1h(None{}, input, write) == write : Nat}:
  {==}

def Facts.facts_cache_write_1h_own_rate(input, write):
  pf.facts_cache_write_1h_own_rate(input, write)
