# eukhe: the proof of LAW admission_run_exact
# Op by op: each op of the model is the spec's (admission_step_exact).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ../../laws/admission/runs.bend as AdmissionRuns
import ./admission_step_exact.bend as PSE

def par.run(os: List<&2, Ad.Op>, +s: Ad.St) -> {Ad.run(os, s) == AdmissionRuns.ads_run(os, s) : Ad.St}:
  match os:
    case Nil{}:
      {==}
    case +o <> r:
      %PSE.pas.step(s, o) : {Ad.run(r, Ad.step(s, o)) == AdmissionRuns.ads_run(r, _) : Ad.St}
      par.run(r, Ad.step(s, o))

def AdmissionRuns.admission_run_exact(os, s):
  par.run(os, s)
