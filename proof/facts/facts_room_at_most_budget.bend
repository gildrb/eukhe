# eukhe: the proof of LAW facts_room_at_most_budget
#
# PROOF: the smaller of b and the room is at most b.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def Facts.facts_room_at_most_budget(b, m, a):
  LNat.rp.min_le(b, Nat.sub(m, a))
