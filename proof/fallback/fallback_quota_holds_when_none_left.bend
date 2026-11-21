# eukhe: the proof of LAW fallback_quota_holds_when_none_left
#
# PROOF: a usage limit never keeps; with every candidate tried there is no
# first untried one (LA.fbb.first_none), and none left holds until the
# reset.

import Base
import ../../bend/fallback.bend as Fb
import ../../laws/fallback.bend as Fallback
import ./base.bend as LA

def Fallback.fallback_quota_holds_when_none_left(until, cands, tried, h):
  %Equal.sym(Maybe<&2, Nat>, Fb.first(cands, tried), None{}, LA.fbb.first_none(cands, tried, h)) : {Fb.next.of(Fb.Quota{until}, _) == Fb.Hold{until} : Fb.Choice}
  {==}
