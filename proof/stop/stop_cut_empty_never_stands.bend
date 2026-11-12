# eukhe: the proof of LAW stop_cut_empty_never_stands
#
# PROOF: the claim computes: LengthStop continues a cut reply with no text before it reads the window's facts.

import Base
import ../../bend/stop.bend as S
import ../../laws/stop/cut.bend as StopCut

def StopCut.stop_cut_empty_never_stands(b, p, sp, cu):
  {==}
