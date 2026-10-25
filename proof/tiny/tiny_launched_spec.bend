# eukhe: the proof of LAW tiny_launched_spec

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/elect.bend as Tiny

def Tiny.tiny_launched_spec(f, l):
  match f l:
    case Tn.First{} Tn.Bound{}:
      {==}
    case Tn.First{} Tn.Adopted{}:
      {==}
    case Tn.Again{} Tn.Bound{}:
      {==}
    case Tn.Again{} Tn.Adopted{}:
      {==}
