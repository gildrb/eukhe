# eukhe: the proof of LAW quirks_rule_terms_exact

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks

def Quirks.quirks_rule_terms_exact(r):
  match r:
    case If.Rule{l, t, d, v}:
      match l:
        case If.Fam{}:
          ({==}, {==}, {==})
        case If.Mod{}:
          ({==}, {==}, {==})
        case If.Host{}:
          ({==}, {==}, {==})
