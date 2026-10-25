# eukhe: the proof of LAW job_wait_polls_at_rest

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job

def Job.job_wait_polls_at_rest(left):
  match left:
    case 0n:
      {==}
    case 1n+l:
      {==}
