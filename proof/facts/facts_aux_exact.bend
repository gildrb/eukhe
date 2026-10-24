# eukhe: the proof of LAW facts_aux_exact

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def Facts.facts_aux_exact(c, d, a, top):
  match c:
    case Fx.Customs{mi, lo, me, hi}:
      {==}
