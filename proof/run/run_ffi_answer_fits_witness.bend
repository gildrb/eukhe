# eukhe: the proof of LAW run_ffi_answer_fits_witness

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def Laws.run_ffi_answer_fits_witness():
  (Rn.EndStop{}, (Rn.Runs{}, {==}))
