# eukhe: the proof of LAW job_kill_ends_now

import Base
import ../../bend/job.bend as Jb
import ../../LAWS.bend as Laws

def pj.job_kill_ends_now(+cap: Maybe<&2, Nat>, +k: Nat, +d: Nat) -> {Jb.step(cap, Jb.Live{k, d}, Jb.Kill{}) == Jb.Ended{k, d, Jb.Killed{}} : Jb.J}:
  {==}

def Laws.job_kill_ends_now(cap, k, d):
  pj.job_kill_ends_now(cap, k, d)
