# eukhe: the proof of LAW job_ends_once

import Base
import ../../bend/job.bend as Jb
import ../../LAWS.bend as Laws
import ./base.bend as LA

# a live job reports one end iff its events hold one
def pj.once(es: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat) -> {List.length(&2, Jb.End, Jb.ends.go(es, cap, Jb.Live{k, d})) == Jb.once(Jb.has_end(es)) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          +t = Jb.take(cap, k, n)
          pj.once(rest, cap, Nat.add(k, t), Nat.add(d, Nat.sub(n, t)))
        case Jb.Quit{q}:
          %LA.pj.ends_ended(rest, cap, k, d, Jb.Exited{q}) : {1n+List.length(&2, Jb.End, _) == 1n : Nat}
          {==}
        case Jb.Kill{}:
          %LA.pj.ends_ended(rest, cap, k, d, Jb.Killed{}) : {1n+List.length(&2, Jb.End, _) == 1n : Nat}
          {==}
        case Jb.Tick{}:
          pj.once(rest, cap, k, d)

def pj.job_ends_once(+cap: Maybe<&2, Nat>, +es: List<&2, Jb.JEv>) -> {List.length(&2, Jb.End, Jb.ends(cap, es)) == Jb.once(Jb.has_end(es)) : Nat}:
  pj.once(es, cap, 0n, 0n)

def Laws.job_ends_once(cap, es):
  pj.job_ends_once(cap, es)
