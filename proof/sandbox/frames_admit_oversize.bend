# eukhe: the proof of LAW frames_admit_oversize
# Past the limit, the length is not at most it (LAFr.fr.lt_nle).

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base/frames.bend as LAFr

def Sandbox.frames_admit_oversize(max, len, k, over):
  %LAFr.fr.lt_nle(len, max, over) : {Sb.admit.size(_, k) == Sb.Oversize{} : Sb.Verdict}
  {==}
