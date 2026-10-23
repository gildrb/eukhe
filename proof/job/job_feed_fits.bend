# eukhe: the proof of LAW job_feed_fits

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base.bend as L
import ./base.bend as LA

def pj.job_feed_fits(+t: Nat, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +n: Nat, fits: {Nat.is_le(Nat.add(Nat.add(k, d), n), t) == True{} : Bool}) -> {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{n}) : Jb.J}:
  +le = LA.pj.le_sub(Nat.add(k, d), n, t, fits)
  %LA.pj.sub_sub_r(t, k, d) : {Jb.step(cap, Jb.Live{k, d}, Jb.Out{Nat.min(n, _)}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{n}) : Jb.J}
  %L.pj.min_of_le(n, Nat.sub(t, Nat.add(k, d)), le) : {Jb.step(cap, Jb.Live{k, d}, Jb.Out{_}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{n}) : Jb.J}
  {==}

def Job.job_feed_fits(t, cap, k, d, n, fits):
  pj.job_feed_fits(t, cap, k, d, n, fits)
