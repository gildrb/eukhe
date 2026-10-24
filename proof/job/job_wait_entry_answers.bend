# eukhe: the proof of LAW job_wait_entry_answers
# Two Bools: four closed strings, each computes.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../laws/job.bend as Job

def Job.job_wait_entry_answers(due, ready):
  match due ready:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}
