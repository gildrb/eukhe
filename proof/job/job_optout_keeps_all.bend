# eukhe: the proof of LAW job_optout_keeps_all

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ./base.bend as LA

# with the opt-out, nothing is dropped
def pj.optout(es: List<&2, Jb.JEv>, +k: Nat) -> {Jb.J.dropped(Jb.go(es, None{}, Jb.Live{k, 0n})) == 0n : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          %LA.pj.sub_self(n) : {Jb.J.dropped(Jb.go(rest, None{}, Jb.Live{Nat.add(k, n), _})) == 0n : Nat}
          pj.optout(rest, Nat.add(k, n))
        case Jb.Quit{q}:
          %LA.pj.ended(rest, None{}, k, 0n, Jb.Exited{q}) : {Jb.J.dropped(_) == 0n : Nat}
          {==}
        case Jb.Kill{}:
          %LA.pj.ended(rest, None{}, k, 0n, Jb.Killed{}) : {Jb.J.dropped(_) == 0n : Nat}
          {==}
        case Jb.Tick{}:
          pj.optout(rest, k)

def pj.job_optout_keeps_all(es: List<&2, Jb.JEv>) -> {Jb.J.dropped(Jb.run(None{}, es)) == 0n : Nat}:
  pj.optout(es, 0n)

def Job.job_optout_keeps_all(es):
  pj.job_optout_keeps_all(es)
