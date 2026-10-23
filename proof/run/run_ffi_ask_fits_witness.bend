# eukhe: the proof of LAW run_ffi_ask_fits_witness

import Base
import ../../bend/run.bend as Rn
import ../../bend/ffi_run.bend as FRn
import ../../LAWS.bend as Laws

def Laws.run_ffi_ask_fits_witness():
  (FRn.AskEnded{Rn.Ended{False{}, False{}}}, {==})
