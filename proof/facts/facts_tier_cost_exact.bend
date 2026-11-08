# eukhe: the proof of LAW facts_tier_cost_exact

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts

def pf.facts_tier_cost_exact(+base: Nat, p: Maybe<&2, Nat>) -> {Fx.tier_cost(base, p) == Facts.tier_cost_spec(base, p) : Nat}:
  match p:
    case Some{k}:
      {==}
    case None{}:
      {==}

def Facts.facts_tier_cost_exact(base, p):
  pf.facts_tier_cost_exact(base, p)
