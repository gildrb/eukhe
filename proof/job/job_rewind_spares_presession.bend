# eukhe: the proof of LAW job_rewind_spares_presession
# Every target tree holds a job that started before any entry.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job

def Job.job_rewind_spares_presession(t):
  {==}
