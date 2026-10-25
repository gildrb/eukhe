# eukhe: the proof of LAW tiny_shut_spec

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/elect.bend as Tiny

def Tiny.tiny_shut_spec(h):
  match h:
    case Tn.Bye{}:
      {==}
    case Tn.Other{}:
      {==}
    case Tn.Eof{}:
      {==}
    case Tn.Lost{}:
      {==}
