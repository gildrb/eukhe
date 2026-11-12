# eukhe: the proof of LAW stop_rounds_note_near_the_cap
#
# PROOF: the rounds left are l (LA.stb.sub_zero, LA.stb.sub_add), at most 10 by the premise.

import Base
import ../../bend/stop.bend as S
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_rounds_note_near_the_cap(d, l, near):
  %Equal.sym(Nat, Nat.sub(Nat.add(d, l), 0n), Nat.add(d, l), LA.stb.sub_zero(Nat.add(d, l))) : {Stop.is_some(S.rounds.at(Nat.is_le(Nat.sub(_, d), 10n), Nat.sub(_, d), 1n+Nat.add(d, l))) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(Nat.add(d, l), d), l, LA.stb.sub_add(d, l)) : {Stop.is_some(S.rounds.at(Nat.is_le(_, 10n), _, 1n+Nat.add(d, l))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(l, 10n), True{}, near) : {Stop.is_some(S.rounds.at(_, l, 1n+Nat.add(d, l))) == True{} : Bool}
  {==}
