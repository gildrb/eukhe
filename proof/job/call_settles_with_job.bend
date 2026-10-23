# eukhe: the proof of LAW call_settles_with_job

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pj.is_settled(m: Maybe<&2, Jb.Wait>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{w}:
      match w:
        case Jb.Settled{x}:
          True{}
        case Jb.Detached{}:
          False{}

def pj.end_of(m: Maybe<&2, Jb.Wait>) -> Jb.End:
  match m:
    case None{}:
      Jb.Killed{}
    case Some{w}:
      match w:
        case Jb.Settled{x}:
          x
        case Jb.Detached{}:
          Jb.Killed{}

# an answer that settled is a settle
def pj.settled(-m: Maybe<&2, Jb.Wait>, -x: Jb.End, s: {m == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}) -> {pj.is_settled(m) == True{} : Bool}:
  Equal.cong(Maybe<&2, Jb.Wait>, Bool, w => pj.is_settled(w), m, Some{Jb.Settled{x}}, s)

# an answer that settled carries its end
def pj.end_eq(-m: Maybe<&2, Jb.Wait>, -x: Jb.End, s: {m == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}) -> {pj.end_of(m) == x : Jb.End}:
  Equal.cong(Maybe<&2, Jb.Wait>, Jb.End, w => pj.end_of(w), m, Some{Jb.Settled{x}}, s)

def pj.settle(es: List<&2, Jb.JEv>, +b: Nat, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End, s: {Jb.wait(es, b) == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}) -> {Jb.ends.go(es, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}:
  match es:
    case Nil{}:
      match b:
        case 0n:
          LLogicLogic.pj.absurdF({Nil{} == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
        case 1n+l:
          LLogicLogic.pj.absurdF({Nil{} == [x] : List<&2, Jb.End>}, pj.settled(None{}, x, s))
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          match b:
            case 0n:
              LLogicLogic.pj.absurdF({Jb.ends.go(Jb.Out{n} <> rest, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
            case 1n+l:
              +t = Jb.take(cap, k, n)
              pj.settle(rest, 1n+l, cap, Nat.add(k, t), Nat.add(d, Nat.sub(n, t)), x, s)
        case Jb.Quit{+q}:
          match b:
            case 0n:
              LLogicLogic.pj.absurdF({Jb.ends.go(Jb.Quit{q} <> rest, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
            case 1n+l:
              %LA.pj.ends_ended(rest, cap, k, d, Jb.Exited{q}) : {Jb.Exited{q} <> _ == [x] : List<&2, Jb.End>}
              %pj.end_eq(Some{Jb.Settled{Jb.Exited{q}}}, x, s) : {[Jb.Exited{q}] == [_] : List<&2, Jb.End>}
              {==}
        case Jb.Kill{}:
          match b:
            case 0n:
              LLogicLogic.pj.absurdF({Jb.ends.go(Jb.Kill{} <> rest, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
            case 1n+l:
              %LA.pj.ends_ended(rest, cap, k, d, Jb.Killed{}) : {Jb.Killed{} <> _ == [x] : List<&2, Jb.End>}
              %pj.end_eq(Some{Jb.Settled{Jb.Killed{}}}, x, s) : {[Jb.Killed{}] == [_] : List<&2, Jb.End>}
              {==}
        case Jb.Tick{}:
          match b:
            case 0n:
              LLogicLogic.pj.absurdF({Jb.ends.go(Jb.Tick{} <> rest, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
            case 1n+l:
              pj.settle(rest, l, cap, k, d, x, s)

def pj.call_settles_with_job(+cap: Maybe<&2, Nat>, +b: Nat, +es: List<&2, Jb.JEv>, +x: Jb.End, settled: {Jb.wait(es, b) == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}) -> {Jb.ends(cap, es) == [x] : List<&2, Jb.End>}:
  pj.settle(es, b, cap, 0n, 0n, x, settled)

def Job.call_settles_with_job(cap, b, es, x, settled):
  pj.call_settles_with_job(cap, b, es, x, settled)
