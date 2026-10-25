# eukhe: the proof of LAW quirks_applies_exact

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks

def Quirks.quirks_applies_exact(q, r):
  match q:
    case If.Query{f, m, h}:
      match r:
        case If.Rule{l, t, d, v}:
          match l:
            case If.Fam{}:
              {==}
            case If.Mod{}:
              {==}
            case If.Host{}:
              {==}
