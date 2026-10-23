# eukhe: the proof of LAW job_no_silent_loss

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ./base.bend as LA

# the bytes kept plus dropped grow by every byte written before the end
def pj.loss(es: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat) -> {Nat.add(Nat.add(k, d), Jb.produced(es)) == Nat.add(Jb.J.kept(Jb.go(es, cap, Jb.Live{k, d})), Jb.J.dropped(Jb.go(es, cap, Jb.Live{k, d}))) : Nat}:
  match es:
    case Nil{}:
      %LA.pj.add_zero(Nat.add(k, d)) : {_ == Nat.add(k, d) : Nat}
      {==}
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          +t = Jb.take(cap, k, n)
          +p = Jb.produced(rest)
          %pj.loss(rest, cap, Nat.add(k, t), Nat.add(d, Nat.sub(n, t))) : {Nat.add(Nat.add(k, d), Nat.add(n, p)) == _ : Nat}
          %LA.pj.split(k, d, t, n, LA.pj.take_le(cap, k, n)) : {Nat.add(Nat.add(k, d), Nat.add(n, p)) == Nat.add(_, p) : Nat}
          %LA.pj.add_assoc(Nat.add(k, d), n, p) : {_ == Nat.add(Nat.add(Nat.add(k, d), n), p) : Nat}
          {==}
        case Jb.Quit{q}:
          %LA.pj.ended(rest, cap, k, d, Jb.Exited{q}) : {Nat.add(Nat.add(k, d), 0n) == Nat.add(Jb.J.kept(_), Jb.J.dropped(_)) : Nat}
          %LA.pj.add_zero(Nat.add(k, d)) : {_ == Nat.add(k, d) : Nat}
          {==}
        case Jb.Kill{}:
          %LA.pj.ended(rest, cap, k, d, Jb.Killed{}) : {Nat.add(Nat.add(k, d), 0n) == Nat.add(Jb.J.kept(_), Jb.J.dropped(_)) : Nat}
          %LA.pj.add_zero(Nat.add(k, d)) : {_ == Nat.add(k, d) : Nat}
          {==}
        case Jb.Tick{}:
          pj.loss(rest, cap, k, d)

def pj.job_no_silent_loss(+cap: Maybe<&2, Nat>, +es: List<&2, Jb.JEv>) -> {Nat.add(Jb.J.kept(Jb.run(cap, es)), Jb.J.dropped(Jb.run(cap, es))) == Jb.produced(es) : Nat}:
  Equal.sym(Nat, Jb.produced(es), Nat.add(Jb.J.kept(Jb.run(cap, es)), Jb.J.dropped(Jb.run(cap, es))), pj.loss(es, cap, 0n, 0n))

def Job.job_no_silent_loss(cap, es):
  pj.job_no_silent_loss(cap, es)
