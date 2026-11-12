# eukhe: the proof of LAW stop_rounds_note_once_none_left
#
# PROOF: past the cap no round is left (LA.stb.sub_zero, LA.stb.sub_past): 0 is at most 10.

import Base
import ../../bend/stop.bend as S
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_rounds_note_once_none_left(m, x):
  match m:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(Nat, Nat.sub(k, 0n), k, LA.stb.sub_zero(k)) : {Stop.is_some(S.rounds.at(Nat.is_le(Nat.sub(_, 1n+Nat.add(k, x)), 10n), Nat.sub(_, 1n+Nat.add(k, x)), 1n+k)) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(k, 1n+Nat.add(k, x)), 0n, LA.stb.sub_past(k, x)) : {Stop.is_some(S.rounds.at(Nat.is_le(_, 10n), _, 1n+k)) == True{} : Bool}
      {==}
