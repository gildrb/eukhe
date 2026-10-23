# eukhe: the proof of LAW facts_tier_price_no_row_base

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws

def pf.facts_tier_price_no_row_base(+rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat, +base: Nat, none: {Fx.price(rows, m, t) == None{} : Maybe<&2, Nat>}) -> {Fx.tier_cost(base, Fx.price(rows, m, t)) == Nat.mul(base, 100n) : Nat}:
  %Equal.sym(Maybe<&2, Nat>, Fx.price(rows, m, t), None{}, none) : {Fx.tier_cost(base, _) == Nat.mul(base, 100n) : Nat}
  {==}

def Laws.facts_tier_price_no_row_base(rows, m, t, base, none):
  pf.facts_tier_price_no_row_base(rows, m, t, base, none)
