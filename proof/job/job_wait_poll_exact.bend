# eukhe: the proof of LAW job_wait_poll_exact

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job

def Job.job_wait_poll_exact(due, ready):
  match due ready:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}
