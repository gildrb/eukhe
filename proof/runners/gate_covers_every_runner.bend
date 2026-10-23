# eukhe: the proof of LAW gate_covers_every_runner

import Base
import ../../bend/runners.bend as Ru
import ../../laws/runners.bend as Runners
import ./base.bend as LA

def pr.MD(m: Maybe<&2, Ru.Tool>, n: Type, s: Type) -> Type:
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
def pr.cover(xs: List<&2, Ru.Tool>, i: Nat, +t: Ru.Tool, cov: {Ru.covered(xs) == True{} : Bool}, at: {List.get(&2, Ru.Tool, xs, i) == Some{t} : Maybe<&2, Ru.Tool>}, runs: {Ru.runs(t) == True{} : Bool}) -> {Ru.gated(t) == True{} : Bool}:
  match xs:
    case Nil{}:
      %at : pr.MD(_, Unit, {Ru.gated(t) == True{} : Bool})
      Unit{}
    case +x <> +rest:
      match i:
        case 0n:
          +same = Equal.cong(Maybe<&2, Ru.Tool>, Ru.Tool, m => Maybe.default(&2, Ru.Tool, m, t), Some{x}, Some{t}, at)
          %same : {Ru.gated(_) == True{} : Bool}
          pr.imp(Ru.runs(x), Ru.gated(x), runners.pr.and_l(Bool.or(Bool.not(Ru.runs(x)), Ru.gated(x)), Ru.covered(rest), cov), Equal.trans(Bool, Ru.runs(x), Ru.runs(t), True{}, Equal.cong(Ru.Tool, Bool, s => Ru.runs(s), x, t, same), runs))
        case 1n+p:
          pr.cover(rest, p, t, runners.pr.and_r(Bool.or(Bool.not(Ru.runs(x)), Ru.gated(x)), Ru.covered(rest), cov), at, runs)

def pr.covers(chat: Bool, i: Nat, +t: Ru.Tool, at: {List.get(&2, Ru.Tool, Ru.registry(chat), i) == Some{t} : Maybe<&2, Ru.Tool>}, runs: {Ru.runs(t) == True{} : Bool}) -> {Ru.gated(t) == True{} : Bool}:
  match chat:
    case True{}:
      pr.cover(Ru.registry(True{}), i, t, {==}, at, runs)
    case False{}:
      pr.cover(Ru.registry(False{}), i, t, {==}, at, runs)

# (G4) Every runner of code goes through the gate

def Runners.gate_covers_every_runner(chat, i, t, at, runs):
  pr.covers(chat, i, t, at, runs)
