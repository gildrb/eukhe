# eukhe: the proof of LAW job_ends_of_exact

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep

def JobStep.job_ends_of_exact(cap, j, e):
  match j e:
    case Jb.Live{k, d} Jb.Out{n}:
      {==}
    case Jb.Live{k, d} Jb.Quit{c}:
      {==}
    case Jb.Live{k, d} Jb.Kill{}:
      {==}
    case Jb.Live{k, d} Jb.Tick{}:
      {==}
    case Jb.Ended{k, d, x} _:
      {==}
