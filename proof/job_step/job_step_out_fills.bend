# eukhe: the proof of LAW job_step_out_fills

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../job/base.bend as LA
import ./base.bend as LJs

def JobStep.job_step_out_fills(c, k, d, n, below, over):
  %LJs.js.min_ge(n, Nat.sub(c, k), LJs.js.sub_le(k, c, n, over)) : {Nat.add(k, _) == c : Nat}
  Equal.sym(Nat, c, Nat.add(k, Nat.sub(c, k)), LA.pj.add_sub(k, c, below))
