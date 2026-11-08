# eukhe: the proof of LAW facts_fit_budget_cut_only_for_answer
#
# PROOF: the fitted budget is min(b, ceiling - a): LA.fr.cut at the ceiling.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def Facts.facts_fit_budget_cut_only_for_answer(base, mm, b, a, win, h):
  LA.fr.cut(b, Fx.cap.shrink(Fx.fit.cap(base, mm, b), win), a, h)
