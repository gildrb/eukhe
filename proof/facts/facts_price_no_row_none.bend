# eukhe: the proof of LAW facts_price_no_row_none
#
# PROOF: both lookups find nothing (LA.fp.none_m, LA.fp.none_a).

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def Facts.facts_price_no_row_none(rows, m, t, none, wide):
  Equal.trans(Maybe<&2, Nat>, Fx.price.or(Fx.price.find(rows, m, t, True{}), Fx.price.find(rows, m, t, False{})), Fx.price.find(rows, m, t, False{}), None{}, LA.fp.or_none(Fx.price.find(rows, m, t, True{}), LA.fp.none_m(rows, m, t, none), Fx.price.find(rows, m, t, False{})), LA.fp.none_a(rows, m, t, wide))
