# eukhe: the proof of LAW fallback_listed_complete
#
# PROOF: induction on the keys before k; at k, Key.eq(k, k) holds field by
# field (afh.listed_in).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback/model.bend as AuxFallback
import ./base/session.bend as LS

def AuxFallback.fallback_listed_complete(a, k, b):
  LS.afh.listed_in(a, k, b)
