# eukhe: the proof of LAW fallback_ends_when_none_left
#
# PROOF: past a keep (LA.fbb.past_keep), with every candidate and every
# default tried (LA.fbb.all_in_app) there is no first untried model
# (LA.fbb.first_none), and none left ends every failure but a usage limit
# with that failure (LA.fbb.none_ends).

import Base
import ../../bend/fallback.bend as Fb
import ../../laws/fallback.bend as Fallback
import ./base.bend as LA

def Fallback.fallback_ends_when_none_left(k, hk, hq, cands, defaults, tried, h, hd):
  %LA.fbb.past_keep(k, cands, defaults, tried, hk) : {_ == Fb.End{k} : Fb.Choice}
  %Equal.sym(Maybe<&2, Nat>, Fb.first(List.append(&2, Nat, cands, defaults), tried), None{}, LA.fbb.first_none(List.append(&2, Nat, cands, defaults), tried, LA.fbb.all_in_app(cands, defaults, tried, h, hd))) : {Fb.next.of(k, _) == Fb.End{k} : Fb.Choice}
  LA.fbb.none_ends(k, hq)
