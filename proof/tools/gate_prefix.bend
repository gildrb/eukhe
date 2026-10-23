# eukhe: the proof of LAW gate_prefix

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pl.step_refl(s: Tl.Step) -> {Tl.step.eq(s, s) == True{} : Bool}:
  match s:
    case Tl.Step{+i, +f}:
      %LA.tools.pl.eq_refl(i) : {Bool.and(_, Tl.ids.eq(f, f)) == True{} : Bool}
      LA.pl.ids_refl(f)

def pl.prefix_cons(+s: Tl.Step, xs: List<&2, Tl.Step>, ys: List<&2, Tl.Step>, h: {Tl.prefix(xs, ys) == True{} : Bool}) -> {Tl.prefix(s <> xs, s <> ys) == True{} : Bool}:
  %Equal.sym(Bool, Tl.step.eq(s, s), True{}, pl.step_refl(s)) : {Bool.and(_, Tl.prefix(xs, ys)) == True{} : Bool}
  h

# what ran is a prefix of the script, at any head test
def pl.prefix_go(ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, free: Bool, +ans: List<&2, Bool>) -> {Tl.prefix(Tl.Ran.steps(Tl.exec.go(ss, auto, free, ans)), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      match free:
        case True{}:
          %LA.pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)) : {Tl.prefix(_, s <> rest) == True{} : Bool}
          pl.prefix_cons(s, Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)), rest, pl.prefix_go(rest, auto, Tl.free.at(rest, auto), ans))
        case False{}:
          match ans:
            case Nil{}:
              %LA.pl.gate_no(s, Tl.Ran{Nil{}, Tl.Finished{}}) : {Tl.prefix(_, s <> rest) == True{} : Bool}
              {==}
            case +a <> +more:
              match a:
                case True{}:
                  %LA.pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {Tl.prefix(_, s <> rest) == True{} : Bool}
                  pl.prefix_cons(s, Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)), rest, pl.prefix_go(rest, auto, Tl.free.at(rest, auto), more))
                case False{}:
                  %LA.pl.gate_no(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {Tl.prefix(_, s <> rest) == True{} : Bool}
                  {==}

def pl.gate_prefix(+ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, ans: List<&2, Bool>) -> {Tl.prefix(Tl.Ran.steps(Tl.exec(ss, auto, ans)), ss) == True{} : Bool}:
  pl.prefix_go(ss, auto, Tl.free.at(ss, auto), ans)

def Tools.gate_prefix(ss, auto, ans):
  pl.gate_prefix(ss, auto, ans)
