# eukhe: the proof of LAW fallback_switches_first_untried
#
# PROOF: past a keep the run takes the first untried candidate
# (LA.fbb.past_keep); every model of p is tried and c is not, so that
# candidate is c (LA.fbb.first_after, by induction on p).

import Base
import ../../bend/fallback.bend as Fb
import ../../laws/fallback.bend as Fallback
import ./base.bend as LA

def Fallback.fallback_switches_first_untried(k, hk, p, c, rest, tried, hp, hc):
  %LA.fbb.past_keep(k, List.append(&2, Nat, p, c <> rest), tried, hk) : {_ == Fb.Switch{c} : Fb.Choice}
  %Equal.sym(Maybe<&2, Nat>, Fb.first(List.append(&2, Nat, p, c <> rest), tried), Some{c}, LA.fbb.first_after(p, c, rest, tried, hp, hc)) : {Fb.next.of(k, _) == Fb.Switch{c} : Fb.Choice}
  {==}
