# eukhe: the proof of LAW gate_needs_yes

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

# every gated step that ran used one approval; free is the head test
def pl.yes_go(ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, free: Bool, +ans: List<&2, Bool>, e: {Tl.free.at(ss, auto) == free : Bool}) -> {Nat.is_le(Tl.gated(Tl.Ran.steps(Tl.exec.go(ss, auto, free, ans)), auto), Tl.yeses(ans)) == True{} : Bool}:
  match ss:
    case Nil{}:
      LA.pl.le0(Tl.yeses(ans))
    case +s <> +rest:
      match free:
        case True{}:
          %LA.pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)) : {Nat.is_le(Tl.gated(_, auto), Tl.yeses(ans)) == True{} : Bool}
          %Equal.sym(Bool, Tl.auto.at(auto, s), True{}, e) : {Nat.is_le(Nat.add(Tl.gated.one(_), Tl.gated(Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)), auto)), Tl.yeses(ans)) == True{} : Bool}
          pl.yes_go(rest, auto, Tl.free.at(rest, auto), ans, {==})
        case False{}:
          match ans:
            case Nil{}:
              %LA.pl.gate_no(s, Tl.Ran{Nil{}, Tl.Finished{}}) : {Nat.is_le(Tl.gated(_, auto), Tl.yeses(Nil{})) == True{} : Bool}
              {==}
            case +a <> +more:
              match a:
                case True{}:
                  %LA.pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {Nat.is_le(Tl.gated(_, auto), Tl.yeses(True{} <> more)) == True{} : Bool}
                  %Equal.sym(Bool, Tl.auto.at(auto, s), False{}, e) : {Nat.is_le(Nat.add(Tl.gated.one(_), Tl.gated(Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)), auto)), Tl.yeses(True{} <> more)) == True{} : Bool}
                  pl.yes_go(rest, auto, Tl.free.at(rest, auto), more, {==})
                case False{}:
                  %LA.pl.gate_no(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {Nat.is_le(Tl.gated(_, auto), Tl.yeses(False{} <> more)) == True{} : Bool}
                  LA.pl.le0(Tl.yeses(more))

def pl.gate_needs_yes(+ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>) -> {Nat.is_le(Tl.gated(Tl.Ran.steps(Tl.exec(ss, auto, ans)), auto), Tl.yeses(ans)) == True{} : Bool}:
  pl.yes_go(ss, auto, Tl.free.at(ss, auto), ans, {==})

def Tools.gate_needs_yes(ss, auto, ans):
  pl.gate_needs_yes(ss, auto, ans)
