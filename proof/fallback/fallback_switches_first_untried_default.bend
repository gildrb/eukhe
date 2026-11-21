# eukhe: the proof of LAW fallback_switches_first_untried_default
#
# PROOF: past a keep the run takes the first untried model of the
# candidates, then the defaults (LA.fbb.past_keep); every candidate is
# tried, so that model is the first untried default (LA.fbb.first_skip);
# every model of p is tried and d is not, so it is d (LA.fbb.first_after).

import Base
import ../../bend/fallback.bend as Fb
import ../../laws/fallback.bend as Fallback
import ./base.bend as LA

def Fallback.fallback_switches_first_untried_default(k, hk, cands, p, d, rest, tried, hcs, hp, hd):
  %LA.fbb.past_keep(k, cands, List.append(&2, Nat, p, d <> rest), tried, hk) : {_ == Fb.Switch{d} : Fb.Choice}
  %Equal.sym(Maybe<&2, Nat>, Fb.first(List.append(&2, Nat, cands, List.append(&2, Nat, p, d <> rest)), tried), Fb.first(List.append(&2, Nat, p, d <> rest), tried), LA.fbb.first_skip(cands, List.append(&2, Nat, p, d <> rest), tried, hcs)) : {Fb.next.of(k, _) == Fb.Switch{d} : Fb.Choice}
  %Equal.sym(Maybe<&2, Nat>, Fb.first(List.append(&2, Nat, p, d <> rest), tried), Some{d}, LA.fbb.first_after(p, d, rest, tried, hp, hd)) : {Fb.next.of(k, _) == Fb.Switch{d} : Fb.Choice}
  {==}
