# eukhe: the proof of LAW run_ffi_ask_fits_witness

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def Run.run_ffi_ask_fits_witness():
  (FRn.AskEnded{Rn.Ended{False{}, False{}}}, {==})
