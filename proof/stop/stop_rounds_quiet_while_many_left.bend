# eukhe: the proof of LAW stop_rounds_quiet_while_many_left
#
# PROOF: the rounds left are 11 + x (LA.stb.sub_zero, LA.stb.sub_add), past the threshold of 10.

import Base
import ../../bend/stop.bend as S
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_rounds_quiet_while_many_left(d, x):
  %Equal.sym(Nat, Nat.sub(Nat.add(d, 11n+x), 0n), Nat.add(d, 11n+x), LA.stb.sub_zero(Nat.add(d, 11n+x))) : {S.rounds.at(Nat.is_le(Nat.sub(_, d), 10n), Nat.sub(_, d), 1n+Nat.add(d, 11n+x)) == None{} : Maybe<&2, String>}
  %Equal.sym(Nat, Nat.sub(Nat.add(d, 11n+x), d), 11n+x, LA.stb.sub_add(d, 11n+x)) : {S.rounds.at(Nat.is_le(_, 10n), _, 1n+Nat.add(d, 11n+x)) == None{} : Maybe<&2, String>}
  {==}
