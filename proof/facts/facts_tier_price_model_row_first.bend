# eukhe: the proof of LAW facts_tier_price_model_row_first

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

# Prices
# ------

def pf.facts_tier_price_model_row_first(+rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat, +k: Nat, hit: {Fx.price.find(rows, m, t, True{}) == Some{k} : Maybe<&2, Nat>}) -> {Fx.price(rows, m, t) == Some{k} : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, Fx.price.find(rows, m, t, True{}), Some{k}, hit) : {Fx.price.or(_, Fx.price.find(rows, m, t, False{})) == Some{k} : Maybe<&2, Nat>}
  {==}

def Facts.facts_tier_price_model_row_first(rows, m, t, k, hit):
  pf.facts_tier_price_model_row_first(rows, m, t, k, hit)
