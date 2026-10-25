# eukhe: the proof of LAW main_roster_read_or_workers

import Base
import ../../bend/runners.bend as Ru
import ../../laws/runners.bend as Runners
import ../base/logic/bool.bend as LLogicBool

def mr.MD(m: Maybe<&2, Ru.Tool>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

# every tool of xs may be on main's roster
def mr.all(xs: List<&2, Ru.Tool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Runners.main_ok(x), mr.all(rest))

# every tool of a list whose tools may all be on main's roster may be
def mr.each(xs: List<&2, Ru.Tool>, i: Nat, +t: Ru.Tool, all: {mr.all(xs) == True{} : Bool}, at: {List.get(&2, Ru.Tool, xs, i) == Some{t} : Maybe<&2, Ru.Tool>}) -> {Runners.main_ok(t) == True{} : Bool}:
  match xs:
    case Nil{}:
      %at : mr.MD(_, Unit, {Runners.main_ok(t) == True{} : Bool})
      Unit{}
    case +x <> +rest:
      match i:
        case 0n:
          +same = Equal.cong(Maybe<&2, Ru.Tool>, Ru.Tool, m => Maybe.default(&2, Ru.Tool, m, t), Some{x}, Some{t}, at)
          %same : {Runners.main_ok(_) == True{} : Bool}
          LLogicBool.pl.and_l(Runners.main_ok(x), mr.all(rest), all)
        case 1n+p:
          mr.each(rest, p, t, LLogicBool.pl.and_r(Runners.main_ok(x), mr.all(rest), all), at)

def Runners.main_roster_read_or_workers(chat, i, t, at):
  match chat:
    case True{}:
      mr.each(Ru.main_roster(True{}), i, t, {==}, at)
    case False{}:
      mr.each(Ru.main_roster(False{}), i, t, {==}, at)
