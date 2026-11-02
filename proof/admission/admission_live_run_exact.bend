# eukhe: the proof of LAW admission_live_run_exact
# The live run follows the model's run (admission_live_run's lemma al.run),
# which is the spec's (admission_run_exact).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ../../laws/admission/runs.bend as AdmissionRuns
import ./admission_live_run.bend as PLR
import ./admission_run_exact.bend as PRE

def AdmissionRuns.admission_live_run_exact(os, s):
  %PRE.par.run(os, s) : {Ad.Live.run(os, Admission.adl_live(s)) == Admission.adl_live(_) : Ad.Live}
  PLR.al.run(os, s)
