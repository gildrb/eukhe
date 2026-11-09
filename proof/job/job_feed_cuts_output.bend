# eukhe: the proof of LAW job_feed_cuts_output
# A live job steps the output cut to the bytes left below t (at most the
# output: min) and every other event as itself; an ended job stays, as
# the step leaves it.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ./base.bend as LA

def Job.job_feed_cuts_output(t, cap, j, e):
  match j:
    case Jb.Live{+k, +d}:
      match e:
        case Jb.Out{+n}:
          +m = Nat.min(n, Nat.sub(Nat.sub(t, k), d))
          (Jb.Out{m}, ((m, ({==}, LA.pj.min_le_l(n, Nat.sub(Nat.sub(t, k), d)))), {==}))
        case Jb.Quit{+c}:
          (Jb.Quit{c}, ({==}, {==}))
        case Jb.Kill{}:
          (Jb.Kill{}, ({==}, {==}))
        case Jb.Tick{}:
          (Jb.Tick{}, ({==}, {==}))
    case Jb.Ended{k, d, x}:
      match e:
        case Jb.Out{+n}:
          (Jb.Out{n}, ((n, ({==}, LA.pj.le_refl(n))), {==}))
        case Jb.Quit{+c}:
          (Jb.Quit{c}, ({==}, {==}))
        case Jb.Kill{}:
          (Jb.Kill{}, ({==}, {==}))
        case Jb.Tick{}:
          (Jb.Tick{}, ({==}, {==}))
