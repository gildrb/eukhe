# eukhe: the proof of LAW run_ffi_ask_fits_witness

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/run/state.bend as RnState
import ../../laws/run.bend as Run

def Run.run_ffi_ask_fits_witness():
  (FRn.AskEnded{RnState.Ended{False{}, False{}}}, {==})
