# eukhe: the proof of LAW job_out_stays_live
# The output is stepped as a part m of it; the step on output adds the
# bytes taken to the kept and the rest to the dropped.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ./base.bend as LA

def JobStep.job_out_stays_live(t, cap, k, d, n):
  +m = Nat.min(n, Nat.sub(Nat.sub(t, k), d))
  +tk = Jb.take(cap, k, m)
  (Nat.add(k, tk), (Nat.add(d, Nat.sub(m, tk)), ({==}, (LA.js.le_add(k, tk), (LA.js.le_add(d, Nat.sub(m, tk)), {==})))))
