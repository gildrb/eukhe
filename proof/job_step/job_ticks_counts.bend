# eukhe: the proof of LAW job_ticks_counts
# Induction on the first list: a tick adds one, any other event none.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ./base.bend as LA

def jt.app(xs: List<&2, Jb.JEv>, +ys: List<&2, Jb.JEv>) -> {Jb.ticks(List.append(&2, Jb.JEv, xs, ys)) == Nat.add(Jb.ticks(xs), Jb.ticks(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Jb.Out{n}:
          jt.app(rest, ys)
        case Jb.Quit{c}:
          jt.app(rest, ys)
        case Jb.Kill{}:
          jt.app(rest, ys)
        case Jb.Tick{}:
          %jt.app(rest, ys) : {1n+Jb.ticks(List.append(&2, Jb.JEv, rest, ys)) == 1n+_ : Nat}
          {==}

def JobStep.job_ticks_counts(xs, ys, n, c):
  (jt.app(xs, ys), ({==}, ({==}, ({==}, {==}))))
