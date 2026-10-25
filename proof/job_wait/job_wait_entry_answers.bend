# eukhe: the proof of LAW job_wait_entry_answers
# A spelled event is a closed string: the entry reads its tag and steps
# the wait as the laws do (JWB.jwb.step).

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

def JobWait.job_wait_entry_answers(w, e):
  match e:
    case None{}:
      JWB.jwb.step(w, False{})
    case Some{x}:
      JWB.jwb.step(w, True{})
