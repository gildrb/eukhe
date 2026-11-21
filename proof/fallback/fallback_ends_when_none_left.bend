# eukhe: the proof of LAW fallback_ends_when_none_left
#
# PROOF: past a keep (LA.fbb.past_keep), with every candidate tried there
# is no first untried one (LA.fbb.first_none), and none left ends every
# failure but a usage limit (LA.fbb.none_ends).

import Base
import ../../bend/fallback.bend as Fb
import ../../laws/fallback.bend as Fallback
import ./base.bend as LA

def Fallback.fallback_ends_when_none_left(k, hk, hq, cands, tried, h):
  %LA.fbb.past_keep(k, cands, tried, hk) : {_ == Fb.End{} : Fb.Choice}
  %Equal.sym(Maybe<&2, Nat>, Fb.first(cands, tried), None{}, LA.fbb.first_none(cands, tried, h)) : {Fb.next.of(k, _) == Fb.End{} : Fb.Choice}
  LA.fbb.none_ends(k, hq)
