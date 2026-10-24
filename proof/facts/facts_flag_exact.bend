# eukhe: the proof of LAW facts_flag_exact

import Base
import ../../bend/facts.bend as Fx
import ../../bend/infer.bend as If
import ../../laws/facts.bend as Facts

def Facts.facts_flag_exact(a, d):
  match a:
    case If.Known{v}:
      match v:
        case 0n:
          {==}
        case 1n+k:
          match k:
            case 0n:
              {==}
            case 1n+j:
              {==}
    case If.Unknown{}:
      {==}
