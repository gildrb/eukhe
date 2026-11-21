# eukhe: the proof of LAW fallback_switches_first_untried
#
# PROOF: past a keep the run takes the first untried model of the
# candidates, then the defaults (LA.fbb.past_keep); joined, they are p,
# then c, then the rest and the defaults (LA.fbb.app_cons); every model of
# p is tried and c is not, so that model is c (LA.fbb.first_after, by
# induction on p).

import Base
import ../../bend/fallback.bend as Fb
import ../../laws/fallback.bend as Fallback
import ./base.bend as LA

def Fallback.fallback_switches_first_untried(k, hk, p, c, rest, defaults, tried, hp, hc):
  %LA.fbb.past_keep(k, List.append(&2, Nat, p, c <> rest), defaults, tried, hk) : {_ == Fb.Switch{c} : Fb.Choice}
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, p, c <> rest), defaults), List.append(&2, Nat, p, c <> List.append(&2, Nat, rest, defaults)), LA.fbb.app_cons(p, c, rest, defaults)) : {Fb.next(_, tried, k) == Fb.Switch{c} : Fb.Choice}
  %Equal.sym(Maybe<&2, Nat>, Fb.first(List.append(&2, Nat, p, c <> List.append(&2, Nat, rest, defaults)), tried), Some{c}, LA.fbb.first_after(p, c, List.append(&2, Nat, rest, defaults), tried, hp, hc)) : {Fb.next.of(k, _) == Fb.Switch{c} : Fb.Choice}
  {==}
