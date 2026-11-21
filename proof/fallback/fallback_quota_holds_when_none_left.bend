# eukhe: the proof of LAW fallback_quota_holds_when_none_left
#
# PROOF: a usage limit never keeps; with every candidate and every default
# tried (LA.fbb.all_in_app) there is no first untried model
# (LA.fbb.first_none), and none left holds until the reset.

import Base
import ../../bend/fallback.bend as Fb
import ../../laws/fallback.bend as Fallback
import ./base.bend as LA

def Fallback.fallback_quota_holds_when_none_left(until, cands, defaults, tried, h, hd):
  %Equal.sym(Maybe<&2, Nat>, Fb.first(List.append(&2, Nat, cands, defaults), tried), None{}, LA.fbb.first_none(List.append(&2, Nat, cands, defaults), tried, LA.fbb.all_in_app(cands, defaults, tried, h, hd))) : {Fb.next.of(Fb.Quota{until}, _) == Fb.Hold{until} : Fb.Choice}
  {==}
