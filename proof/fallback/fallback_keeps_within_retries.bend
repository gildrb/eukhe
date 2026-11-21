# eukhe: the proof of LAW fallback_keeps_within_retries
#
# PROOF: the model keeps exactly when n <= retries (Fb.kept); the premise
# says it does.

import Base
import ../../bend/fallback.bend as Fb
import ../../laws/fallback.bend as Fallback

def Fallback.fallback_keeps_within_retries(n, retries, cands, tried, h):
  %Equal.sym(Bool, Nat.is_le(n, retries), True{}, h) : {Fb.choose.if(Fb.Failed{n, retries}, cands, tried, _) == Fb.Keep{} : Fb.Choice}
  {==}
