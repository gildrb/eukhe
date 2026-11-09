# eukhe: the proof of LAW worker_tools_main_only

import Base
import ../../bend/runners.bend as Ru
import ../../laws/runners.bend as Runners
import ../base/logic/bool.bend as LLogicBool

def wt.MD(m: Maybe<&2, Ru.ToolReg>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

# no tool of xs is a worker tool
def wt.none(xs: List<&2, Ru.ToolReg>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.not(Runners.worker_tool(x)), wt.none(rest))

# no tool of a list without worker tools is one
def wt.each(xs: List<&2, Ru.ToolReg>, i: Nat, +t: Ru.ToolReg, none: {wt.none(xs) == True{} : Bool}, at: {List.get(&2, Ru.ToolReg, xs, i) == Some{t} : Maybe<&2, Ru.ToolReg>}) -> {Runners.worker_tool(t) == False{} : Bool}:
  match xs:
    case Nil{}:
      %at : wt.MD(_, Unit, {Runners.worker_tool(t) == False{} : Bool})
      Unit{}
    case +x <> +rest:
      match i:
        case 0n:
          +same = Equal.cong(Maybe<&2, Ru.ToolReg>, Ru.ToolReg, m => Maybe.default(&2, Ru.ToolReg, m, t), Some{x}, Some{t}, at)
          %same : {Runners.worker_tool(_) == False{} : Bool}
          LLogicBool.pt.not_f(Runners.worker_tool(x), LLogicBool.pl.and_l(Bool.not(Runners.worker_tool(x)), wt.none(rest), none))
        case 1n+p:
          wt.each(rest, p, t, LLogicBool.pl.and_r(Bool.not(Runners.worker_tool(x)), wt.none(rest), none), at)

def Runners.worker_tools_main_only(i, t, at):
  wt.each(Ru.registry(), i, t, {==}, at)
