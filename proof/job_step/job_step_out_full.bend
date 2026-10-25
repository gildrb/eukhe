# eukhe: the proof of LAW job_step_out_full

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../job/base.bend as LA
import ./base.bend as LJs

def JobStep.job_step_out_full(c, k, d, n, full):
  %LJs.js.sub_zero_le(c, k, full) : {Nat.add(k, Nat.min(n, _)) == k : Nat}
  %LJs.js.min_zero(n) : {Nat.add(k, _) == k : Nat}
  %LA.pj.add_zero(k) : {_ == k : Nat}
  {==}
