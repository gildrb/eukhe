# eukhe: the proof of LAW job_optout_keeps_output
# Below the bound the entry steps the whole output (job_feed_fits); the
# opt-out takes all of it, so n - n = 0 is dropped.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../../laws/job.bend as Job
import ../job/base.bend as LAJob
import ../job/job_feed_fits.bend as PJobFeedFits
import ./base.bend as LA

def JobStep.job_optout_keeps_output(t, k, d, n, fits):
  %Equal.sym(Jb.J, Jb.feed(t, None{}, Jb.Live{k, d}, Jb.Out{n}), Jb.step(None{}, Jb.Live{k, d}, Jb.Out{n}), Job.job_feed_fits(t, None{}, k, d, n, fits)) : {_ == Jb.Live{Nat.add(k, n), d} : Jb.J}
  %LAJob.pj.sub_self(n) : {Jb.Live{Nat.add(k, n), Nat.add(d, _)} == Jb.Live{Nat.add(k, n), d} : Jb.J}
  %LAJob.pj.add_zero(d) : {Jb.Live{Nat.add(k, n), _} == Jb.Live{Nat.add(k, n), d} : Jb.J}
  {==}
