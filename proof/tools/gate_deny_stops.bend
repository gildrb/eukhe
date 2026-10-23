# eukhe: the proof of LAW gate_deny_stops

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pl.ND(n: Nat, z: Type, s: Type) -> Type:
  match n:
    case 0n:
      z
    case 1n+p:
      s

def pl.gate_den(s: Tl.Step, r: Tl.Ran) -> {Tl.gate(False{}, s, r) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  match s:
    case Tl.Step{i, f}:
      {==}

# a free head adds no gated step
def pl.one_zero(b: Bool, -g: Nat, h: {Nat.add(Tl.gated.one(b), g) == 0n : Nat}, hb: {b == True{} : Bool}) -> {g == 0n : Nat}:
  match b:
    case True{}:
      h
    case False{}:
      LLogicLogic.tools.pl.absurdF({g == 0n : Nat}, hb)

# a held head adds a gated step
def pl.one_nz(-A: Type, b: Bool, -g: Nat, h: {Nat.add(Tl.gated.one(b), g) == 0n : Nat}, hb: {b == False{} : Bool}) -> A:
  match b:
    case True{}:
      LA.tools.pl.absurd(A, hb)
    case False{}:
      %h : pl.ND(_, A, Unit)
      Unit{}

# free steps run through to the held step s, which a denial stops
def pl.deny_go(pre: List<&2, Tl.Step>, +s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>, free: Bool, e: {Tl.free.at(List.append(&2, Tl.Step, pre, s <> post), auto) == free : Bool}, gf: {Tl.gated(pre, auto) == 0n : Nat}, held: {Tl.auto.at(auto, s) == False{} : Bool}) -> {Tl.exec.go(List.append(&2, Tl.Step, pre, s <> post), auto, free, False{} <> ans) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  match pre:
    case Nil{}:
      match free:
        case True{}:
          LA.tools.pl.absurd({Tl.exec.go(s <> post, auto, True{}, False{} <> ans) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}, Equal.trans(Bool, True{}, Tl.auto.at(auto, s), False{}, Equal.sym(Bool, Tl.auto.at(auto, s), True{}, e), held))
        case False{}:
          pl.gate_den(s, Tl.exec.go(post, auto, Tl.free.at(post, auto), ans))
    case +p <> +prest:
      match free:
        case True{}:
          Equal.cong(Tl.Ran, Tl.Ran, r => Tl.ran.add(p, r), Tl.exec.go(List.append(&2, Tl.Step, prest, s <> post), auto, Tl.free.at(List.append(&2, Tl.Step, prest, s <> post), auto), False{} <> ans), Tl.Ran{prest, Tl.Denied{Tl.Step.id(s)}}, pl.deny_go(prest, s, post, auto, ans, Tl.free.at(List.append(&2, Tl.Step, prest, s <> post), auto), {==}, pl.one_zero(Tl.auto.at(auto, p), Tl.gated(prest, auto), gf, e), held))
        case False{}:
          pl.one_nz({Tl.exec.go(p <> List.append(&2, Tl.Step, prest, s <> post), auto, False{}, False{} <> ans) == Tl.Ran{p <> prest, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}, Tl.auto.at(auto, p), Tl.gated(prest, auto), gf, e)

def pl.gate_deny_stops(+pre: List<&2, Tl.Step>, +s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, ans: List<&2, Bool>, free: {Tl.gated(pre, auto) == 0n : Nat}, held: {Tl.auto.at(auto, s) == False{} : Bool}) -> {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, False{} <> ans) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  pl.deny_go(pre, s, post, auto, ans, Tl.free.at(List.append(&2, Tl.Step, pre, s <> post), auto), {==}, free, held)

def Tools.gate_deny_stops(pre, s, post, auto, ans, free, held):
  pl.gate_deny_stops(pre, s, post, auto, ans, free, held)
