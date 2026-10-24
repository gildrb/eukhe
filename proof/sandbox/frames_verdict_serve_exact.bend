# eukhe: the proof of LAW frames_verdict_serve_exact

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox

def Sandbox.frames_verdict_serve_exact(v):
  match v:
    case Sb.Serve{}:
      {==}
    case Sb.Duplicate{}:
      {==}
    case Sb.Oversize{}:
      {==}
    case Sb.Kindless{}:
      {==}
    case Sb.NotServed{}:
      {==}
