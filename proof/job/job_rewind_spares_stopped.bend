# eukhe: the proof of LAW job_rewind_spares_stopped
# A job that does not run gets no kill, whatever the tree holds.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job

def Job.job_rewind_spares_stopped(a, target):
  {==}
