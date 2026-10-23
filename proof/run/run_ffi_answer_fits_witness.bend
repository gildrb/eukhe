# eukhe: the proof of LAW run_ffi_answer_fits_witness

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def Run.run_ffi_answer_fits_witness():
  (Rn.EndStop{}, (Rn.Runs{}, {==}))
