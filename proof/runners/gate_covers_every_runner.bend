# eukhe: the proof of LAW gate_covers_every_runner

import Base
import ../../bend/runners.bend as Ru
import ../../laws/runners.bend as Runners
import ./base.bend as LA

def pr.MD(m: Maybe<&2, Ru.ToolReg>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

def runners.pr.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LA.pr.absurdF({b == True{} : Bool}, h)

def runners.pr.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LA.pr.absurdF({False{} == True{} : Bool}, h)

# not a or b, and a: b
def pr.imp(a: Bool, +b: Bool, h: {Bool.or(Bool.not(a), b) == True{} : Bool}, ha: {a == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LA.pr.absurdF({b == True{} : Bool}, ha)

# The registry
# ------------

# every tool of a covered list that runs code is gated
def pr.cover(xs: List<&2, Ru.ToolReg>, i: Nat, +t: Ru.ToolReg, cov: {Ru.covered(xs) == True{} : Bool}, at: {List.get(&2, Ru.ToolReg, xs, i) == Some{t} : Maybe<&2, Ru.ToolReg>}, runs: {Ru.runs(t) == True{} : Bool}) -> {Ru.gated(t) == True{} : Bool}:
  match xs:
    case Nil{}:
      %at : pr.MD(_, Unit, {Ru.gated(t) == True{} : Bool})
      Unit{}
    case +x <> +rest:
      match i:
        case 0n:
          +same = Equal.cong(Maybe<&2, Ru.ToolReg>, Ru.ToolReg, m => Maybe.default(&2, Ru.ToolReg, m, t), Some{x}, Some{t}, at)
          %same : {Ru.gated(_) == True{} : Bool}
          pr.imp(Ru.runs(x), Ru.gated(x), runners.pr.and_l(Bool.or(Bool.not(Ru.runs(x)), Ru.gated(x)), Ru.covered(rest), cov), Equal.trans(Bool, Ru.runs(x), Ru.runs(t), True{}, Equal.cong(Ru.ToolReg, Bool, s => Ru.runs(s), x, t, same), runs))
        case 1n+p:
          pr.cover(rest, p, t, runners.pr.and_r(Bool.or(Bool.not(Ru.runs(x)), Ru.gated(x)), Ru.covered(rest), cov), at, runs)

# (G4) Every runner of code goes through the gate

def Runners.gate_covers_every_runner(i, t, at, runs):
  pr.cover(Ru.registry(), i, t, {==}, at, runs)
