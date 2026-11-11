# eukhe: the proof of LAW quirks_known_exact

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks

def Quirks.quirks_known_exact(a):
  match a:
    case If.Known{v}:
      {==}
    case If.Unknown{}:
      {==}
