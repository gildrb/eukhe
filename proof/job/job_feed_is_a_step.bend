# eukhe: the proof of LAW job_feed_is_a_step

import Base
import ../../laws/job.bend as Job

def Job.job_feed_is_a_step(t, cap, k, d, n):
  (Nat.min(n, Nat.sub(Nat.sub(t, k), d)), {==})
