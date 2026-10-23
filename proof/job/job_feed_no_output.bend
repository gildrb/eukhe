# eukhe: the proof of LAW job_feed_no_output

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base/bool/misc.bend as LBoolMisc

# The step the Rust jobs run (`feed`): below t it is the step; any output
# is a step on a part of it; the counts stay within t and fill it.

def pj.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : LBoolMisc.pj.BD(_, Unit, A)
  Unit{}

def pj.job_feed_no_output(+t: Nat, +cap: Maybe<&2, Nat>, j: Jb.J, e: Jb.JEv, quiet: {Job.JobWrites(e) == False{} : Bool}) -> {Jb.feed(t, cap, j, e) == Jb.step(cap, j, e) : Jb.J}:
  match j:
    case Jb.Live{k, d}:
      match e:
        case Jb.Out{n}:
          pj.absurdT({Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{n}) : Jb.J}, quiet)
        case Jb.Quit{c}:
          {==}
        case Jb.Kill{}:
          {==}
        case Jb.Tick{}:
          {==}
    case Jb.Ended{k, d, x}:
      match e:
        case Jb.Out{n}:
          {==}
        case Jb.Quit{c}:
          {==}
        case Jb.Kill{}:
          {==}
        case Jb.Tick{}:
          {==}

def Job.job_feed_no_output(t, cap, j, e, quiet):
  pj.job_feed_no_output(t, cap, j, e, quiet)
