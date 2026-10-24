# eukhe: the proof of LAW job_step_out_fits

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../base/nat.bend as LNat
import ../job/base.bend as LA

def JobStep.job_step_out_fits(c, k, d, n, fits):
  %LNat.pj.min_of_le(n, Nat.sub(c, k), LA.pj.le_sub(k, n, c, fits)) : {Nat.add(k, _) == Nat.add(k, n) : Nat}
  {==}
