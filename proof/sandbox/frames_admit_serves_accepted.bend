# eukhe: the proof of LAW frames_admit_serves_accepted
# A fresh frame is served exactly when it fits and its kind is allowed
# (LAFr.fr.sa), which is `accepts`.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base/frames.bend as LAFr

def Sandbox.frames_admit_serves_accepted(max, allowed, i, len, k):
  LAFr.fr.sa(Nat.is_le(len, max), Sb.elem(allowed, k))
