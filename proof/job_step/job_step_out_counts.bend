# eukhe: the proof of LAW job_step_out_counts

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../job/base.bend as LA

def JobStep.job_step_out_counts(cap, k, d, n):
  Equal.sym(Nat, Nat.add(Nat.add(k, d), n), Jb.J.total(Jb.step(cap, Jb.Live{k, d}, Jb.Out{n})), LA.pj.out_total(cap, k, d, n))
