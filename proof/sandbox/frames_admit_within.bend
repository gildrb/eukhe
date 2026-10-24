# eukhe: the proof of LAW frames_admit_within
# Within the limit, the type decides (LAFr.fr.kind).

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base/frames.bend as LAFr

def Sandbox.frames_admit_within(max, len, k, fits):
  %Equal.sym(Bool, Nat.is_le(len, max), True{}, fits) : {Sb.admit.size(_, k) == Sandbox.kind_spec(k) : Sb.Verdict}
  LAFr.fr.kind(k)
