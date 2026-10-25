# eukhe: the proof of LAW job_feed_past_bound
# Past the bound the output is cut to 0 bytes, and 0 bytes change nothing.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../job/base.bend as LA
import ./base.bend as LJs

def jpb.zero(cap: Maybe<&2, Nat>, +k: Nat, +d: Nat) -> {Jb.step(cap, Jb.Live{k, d}, Jb.Out{0n}) == Jb.Live{k, d} : Jb.J}:
  match cap:
    case None{}:
      %LA.pj.add_zero(k) : {Jb.Live{_, Nat.add(d, 0n)} == Jb.Live{k, d} : Jb.J}
      %LA.pj.add_zero(d) : {Jb.Live{k, _} == Jb.Live{k, d} : Jb.J}
      {==}
    case Some{c}:
      %LA.pj.add_zero(k) : {Jb.Live{_, Nat.add(d, 0n)} == Jb.Live{k, d} : Jb.J}
      %LA.pj.add_zero(d) : {Jb.Live{k, _} == Jb.Live{k, d} : Jb.J}
      {==}

def JobStep.job_feed_past_bound(t, cap, k, d, n, past):
  %LA.pj.sub_sub_r(t, k, d) : {Jb.step(cap, Jb.Live{k, d}, Jb.Out{Nat.min(n, _)}) == Jb.Live{k, d} : Jb.J}
  %LJs.js.sub_zero_le(t, Nat.add(k, d), LJs.js.lt_le(t, Nat.add(k, d), past)) : {Jb.step(cap, Jb.Live{k, d}, Jb.Out{Nat.min(n, _)}) == Jb.Live{k, d} : Jb.J}
  %LJs.js.min_zero(n) : {Jb.step(cap, Jb.Live{k, d}, Jb.Out{_}) == Jb.Live{k, d} : Jb.J}
  jpb.zero(cap, k, d)
