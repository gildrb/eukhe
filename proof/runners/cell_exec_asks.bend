# eukhe: the proof of LAW cell_exec_asks

import Base
import ../../bend/runners.bend as Ru
import ../../laws/runners.bend as Runners
import ./base.bend as LA

def pr.and_f(a: Bool, +b: Bool, h: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

# a cap list holding exec is not within an auto set without exec
def pr.exec_asks(caps: List<&2, Nat>, +auto: List<&2, Nat>, has: {Ru.elem(caps, Ru.exec()) == True{} : Bool}, lacks: {Ru.elem(auto, Ru.exec()) == False{} : Bool}) -> {Ru.within(caps, auto) == False{} : Bool}:
  match caps:
    case Nil{}:
      LA.pr.absurdF({True{} == False{} : Bool}, has)
    case +c <> +rest:
      match c:
        case 0n:
          pr.and_f(Bool.and(Ru.grantable(0n), Ru.elem(auto, 0n)), Ru.within(rest, auto), pr.exec_asks(rest, auto, has, lacks))
        case 1n+p:
          match p:
            case 0n:
              pr.and_f(Bool.and(Ru.grantable(1n), Ru.elem(auto, 1n)), Ru.within(rest, auto), pr.exec_asks(rest, auto, has, lacks))
            case 1n+q:
              match q:
                case 0n:
                  %Equal.sym(Bool, Ru.elem(auto, 2n), False{}, lacks) : {Bool.and(Bool.and(True{}, _), Ru.within(rest, auto)) == False{} : Bool}
                  {==}
                case 1n+r:
                  pr.and_f(Bool.and(Ru.grantable(3n+r), Ru.elem(auto, 3n+r)), Ru.within(rest, auto), pr.exec_asks(rest, auto, has, lacks))

def Runners.cell_exec_asks(caps, auto, has, lacks):
  pr.exec_asks(caps, auto, has, lacks)
