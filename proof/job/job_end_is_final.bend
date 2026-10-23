# eukhe: the proof of LAW job_end_is_final

import Base
import ../../bend/job.bend as Jb
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def pj.same(+xs: List<&2, Jb.JEv>, +ys: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End) -> {Jb.go(xs, cap, Jb.Ended{k, d, x}) == Jb.go(ys, cap, Jb.Ended{k, d, x}) : Jb.J}:
  %LA.pj.ended(xs, cap, k, d, x) : {_ == Jb.go(ys, cap, Jb.Ended{k, d, x}) : Jb.J}
  LA.pj.ended(ys, cap, k, d, x)

def pj.quit_end(+xs: List<&2, Jb.JEv>, +ys: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, j: Jb.J, +q: Jb.Code) -> {Jb.go(xs, cap, Jb.step(cap, j, Jb.Quit{q})) == Jb.go(ys, cap, Jb.step(cap, j, Jb.Quit{q})) : Jb.J}:
  match j:
    case Jb.Live{k, d}:
      pj.same(xs, ys, cap, k, d, Jb.Exited{q})
    case Jb.Ended{k, d, x}:
      pj.same(xs, ys, cap, k, d, x)

def pj.kill_end(+xs: List<&2, Jb.JEv>, +ys: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, j: Jb.J) -> {Jb.go(xs, cap, Jb.step(cap, j, Jb.Kill{})) == Jb.go(ys, cap, Jb.step(cap, j, Jb.Kill{})) : Jb.J}:
  match j:
    case Jb.Live{k, d}:
      pj.same(xs, ys, cap, k, d, Jb.Killed{})
    case Jb.Ended{k, d, x}:
      pj.same(xs, ys, cap, k, d, x)

# once a prefix holds an end, the rest changes nothing
def pj.final(pre: List<&2, Jb.JEv>, post: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +j: Jb.J, h: {Jb.has_end(pre) == True{} : Bool}) -> {Jb.go(List.append(&2, Jb.JEv, pre, post), cap, j) == Jb.go(pre, cap, j) : Jb.J}:
  match pre:
    case Nil{}:
      L.pj.absurdF({Jb.go(post, cap, j) == j : Jb.J}, h)
    case e <> +rest:
      match e:
        case Jb.Out{n}:
          pj.final(rest, post, cap, Jb.step(cap, j, Jb.Out{n}), h)
        case Jb.Quit{q}:
          pj.quit_end(List.append(&2, Jb.JEv, rest, post), rest, cap, j, q)
        case Jb.Kill{}:
          pj.kill_end(List.append(&2, Jb.JEv, rest, post), rest, cap, j)
        case Jb.Tick{}:
          pj.final(rest, post, cap, Jb.step(cap, j, Jb.Tick{}), h)

def pj.job_end_is_final(+cap: Maybe<&2, Nat>, +pre: List<&2, Jb.JEv>, post: List<&2, Jb.JEv>, ended: {Jb.has_end(pre) == True{} : Bool}) -> {Jb.run(cap, List.append(&2, Jb.JEv, pre, post)) == Jb.run(cap, pre) : Jb.J}:
  pj.final(pre, post, cap, Jb.Live{0n, 0n}, ended)

def Laws.job_end_is_final(cap, pre, post, ended):
  pj.job_end_is_final(cap, pre, post, ended)
