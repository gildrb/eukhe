# eukhe: the proof of LAW stop_cut_example
#
# PROOF: the closed claims compute.

import Base
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../laws/stop/cut.bend as StopCut

def StopCut.stop_cut_example():
  ({==}, ({==}, {==}))
