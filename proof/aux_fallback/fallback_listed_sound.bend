# eukhe: the proof of LAW fallback_listed_sound
#
# PROOF: induction on the list; the first key that Key.eq calls k is k
# (ppr.key_eq_true), the keys before it are the prefix (afh.listed_sound).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback/model.bend as AuxFallback
import ./base/session.bend as LS

def AuxFallback.fallback_listed_sound(ks, k, h):
  LS.afh.listed_sound(ks, k, h)
