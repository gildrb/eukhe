# eukhe: the proof of LAW facts_room_no_room
#
# PROOF: m - a is 0 below a, and the smaller of b and 0 is 0.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def rn.main(+b: Nat, +m: Nat, +a: Nat, +h: {Nat.is_lt(m, a) == True{} : Bool}) -> {Fx.room(b, m, a) == 0n : Nat}:
  %Equal.sym(Nat, Nat.sub(m, a), 0n, LA.pf.sub_zero_lt(m, a, h)) : {Nat.min(b, _) == 0n : Nat}
  LA.pf.min_zero(b)

def Facts.facts_room_no_room(b, m, a, h):
  rn.main(b, m, a, h)
