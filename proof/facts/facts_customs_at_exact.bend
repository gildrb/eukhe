# eukhe: the proof of LAW facts_customs_at_exact

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def Facts.facts_customs_at_exact(c, l):
  match c:
    case Fx.Customs{mi, lo, me, hi}:
      match l:
        case Fx.Minimal{}:
          {==}
        case Fx.Low{}:
          {==}
        case Fx.Medium{}:
          {==}
        case Fx.High{}:
          {==}
