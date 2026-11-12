# eukhe: the proof of LAW stop_cut_text_stands_with_room
#
# PROOF: the claim computes: LengthStop yields at a window with room before it reads the compaction fact, and before any outer Director reads the stop.

import Base
import ../../bend/stop.bend as S
import ../../laws/stop/cut.bend as StopCut

def StopCut.stop_cut_text_stands_with_room(b, p, cu):
  {==}
