# eukhe: the proof of LAW facts_price_wide_row_next
#
# PROOF: the model's lookup finds nothing (LA.fp.none_m), so the price is
# the every-model lookup, which finds the row (LA.fp.first_a).

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def Facts.facts_price_wide_row_next(pre, post, m, t, k, none, first):
  +rows = List.append(&2, Fx.PRow, pre, Fx.PRow{None{}, t, k} <> post)
  Equal.trans(Maybe<&2, Nat>, Fx.price.or(Fx.price.find(rows, m, t, True{}), Fx.price.find(rows, m, t, False{})), Fx.price.find(rows, m, t, False{}), Some{k}, LA.fp.or_none(Fx.price.find(rows, m, t, True{}), LA.fp.none_m(rows, m, t, none), Fx.price.find(rows, m, t, False{})), LA.fp.first_a(pre, post, m, t, k, first))
