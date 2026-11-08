# eukhe: the proof of LAW facts_room_cut_only_for_answer
#
# PROOF: LA.fr.cut, peeling a and m together down to a = 0.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def Facts.facts_room_cut_only_for_answer(b, m, a, fits):
  LA.fr.cut(b, m, a, fits)
