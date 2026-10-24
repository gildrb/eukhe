# eukhe: the proof of LAW tiny_bind_spec

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny.bend as Tiny

def Tiny.tiny_bind_spec(p):
  match p:
    case Tn.Missing{}:
      {==}
    case Tn.Unreachable{}:
      {==}
    case Tn.Pong{t}:
      {==}
    case Tn.Odd{}:
      {==}
    case Tn.Garbled{}:
      {==}
    case Tn.Hung{}:
      {==}
