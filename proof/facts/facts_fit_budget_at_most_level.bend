# eukhe: the proof of LAW facts_fit_budget_at_most_level
#
# PROOF: the fitted budget is the smaller of b and the room under the
# ceiling, at most b.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def Facts.facts_fit_budget_at_most_level(base, mm, b, a, win):
  LNat.rp.min_le(b, Nat.sub(Fx.cap.shrink(Fx.fit.cap(base, mm, b), win), a))
