# eukhe: the proof of LAW gate_finish_runs_all

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pl.fin_add(+s: Tl.Step, r: Tl.Ran, h: {Tl.End.finished(Tl.Ran.end(Tl.ran.add(s, r))) == True{} : Bool}) -> {Tl.End.finished(Tl.Ran.end(r)) == True{} : Bool}:
  match r:
    case Tl.Ran{ss, e}:
      h

def pl.gate_no_fin(-A: Type, s: Tl.Step, r: Tl.Ran, h: {Tl.End.finished(Tl.Ran.end(Tl.gate(False{}, s, r))) == True{} : Bool}) -> A:
  match s:
    case Tl.Step{i, f}:
      LLogicLogic.tools.pl.absurdF(A, h)

# a run that finished ran every step, at any head test
def pl.fin_go(ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, free: Bool, +ans: List<&2, Bool>, h: {Tl.End.finished(Tl.Ran.end(Tl.exec.go(ss, auto, free, ans))) == True{} : Bool}) -> {Tl.Ran.steps(Tl.exec.go(ss, auto, free, ans)) == ss : List<&2, Tl.Step>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      match free:
        case True{}:
          %LA.pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)) : {_ == s <> rest : List<&2, Tl.Step>}
          Equal.cong(List<&2, Tl.Step>, List<&2, Tl.Step>, xs => s <> xs, Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)), rest, pl.fin_go(rest, auto, Tl.free.at(rest, auto), ans, pl.fin_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans), h)))
        case False{}:
          match ans:
            case Nil{}:
              pl.gate_no_fin({Tl.Ran.steps(Tl.gate(False{}, s, Tl.Ran{Nil{}, Tl.Finished{}})) == s <> rest : List<&2, Tl.Step>}, s, Tl.Ran{Nil{}, Tl.Finished{}}, h)
            case +a <> +more:
              match a:
                case True{}:
                  %LA.pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {_ == s <> rest : List<&2, Tl.Step>}
                  Equal.cong(List<&2, Tl.Step>, List<&2, Tl.Step>, xs => s <> xs, Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)), rest, pl.fin_go(rest, auto, Tl.free.at(rest, auto), more, pl.fin_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more), h)))
                case False{}:
                  pl.gate_no_fin({Tl.Ran.steps(Tl.gate(False{}, s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more))) == s <> rest : List<&2, Tl.Step>}, s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more), h)

def pl.gate_finish_runs_all(+ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>, fin: {Tl.End.finished(Tl.Ran.end(Tl.exec(ss, auto, ans))) == True{} : Bool}) -> {Tl.Ran.steps(Tl.exec(ss, auto, ans)) == ss : List<&2, Tl.Step>}:
  pl.fin_go(ss, auto, Tl.free.at(ss, auto), ans, fin)

def Tools.gate_finish_runs_all(ss, auto, ans, fin):
  pl.gate_finish_runs_all(ss, auto, ans, fin)
