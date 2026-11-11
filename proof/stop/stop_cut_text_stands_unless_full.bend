# eukhe: the proof of LAW stop_cut_text_stands_unless_full
#
# PROOF: the closed claims compute: LengthStop yields at room and continues at a full window, before any outer Director reads the stop.

import Base
import ../../bend/stop.bend as S
import ../../laws/stop/cut.bend as StopCut

def StopCut.stop_cut_text_stands_unless_full(b, p):
  ({==}, {==})
