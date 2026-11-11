# eukhe: the proof of LAW job_terms_exact

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep

def JobStep.job_terms_exact(j):
  match j:
    case Jb.Live{k, d}:
      ({==}, ({==}, ({==}, {==})))
    case Jb.Ended{k, d, e}:
      ({==}, ({==}, ({==}, {==})))
