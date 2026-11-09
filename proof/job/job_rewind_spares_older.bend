# eukhe: the proof of LAW job_rewind_spares_older
# The tree at t holds a job that started after a commit below t.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job

def Job.job_rewind_spares_older(t, a, before):
  %Equal.sym(Bool, Nat.is_lt(a, t), True{}, before) : {[Bool.not(_)] == [False{}] : List<&2, Bool>}
  {==}
