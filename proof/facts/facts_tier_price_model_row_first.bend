# eukhe: the proof of LAW facts_tier_price_model_row_first
#
# PROOF: the model's lookup finds the row (LA.fp.first_m), and a hit of
# the model's lookup is the price.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def Facts.facts_tier_price_model_row_first(pre, post, m, t, k, first):
  +rows = List.append(&2, Fx.PRow, pre, Fx.PRow{Some{m}, t, k} <> post)
  LA.fp.or_some(Fx.price.find(rows, m, t, True{}), k, LA.fp.first_m(pre, post, m, t, k, first), Fx.price.find(rows, m, t, False{}))
