# eukhe: the proof of LAW fallback_pass_refused
#
# PROOF: the gate of a selector allowedModels does not admit decides the
# fallback of reason 0; an admitted one is looked up and a miss keeps its
# reason (computation).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback/model.bend as AuxFallback

def AuxFallback.fallback_pass_refused(p, s, look, r, need):
  {==}
