# eukhe: the proof of LAW run_ffi_answer_fits_witness

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run.bend as Run

def Run.run_ffi_answer_fits_witness():
  (RnDecision.EndStop{}, (RnDecision.Runs{}, {==}))
