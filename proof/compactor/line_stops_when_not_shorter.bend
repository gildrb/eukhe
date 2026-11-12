# eukhe: the proof of LAW line_stops_when_not_shorter
# Over the replies the line asked again on, line.go takes one call each
# and goes on from the last of them (LA.lp.go), which it holds as its best
# reply: past the node, its length its bytes (LA.lp.lk). A reply not
# shorter than it is past the node too, so it neither fits nor asks
# again: the line ends with the best reply cut.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def lsn.le_not_lt(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.pc.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      lsn.le_not_lt(p, q, e)

def lsn.lt_le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      LLogicLogic.pc.absurd_ft({Nat.is_lt(0n, c) == True{} : Bool}, ab)
    case 1n+p 0n _:
      LLogicLogic.pc.absurd_ft({Nat.is_lt(1n+p, c) == True{} : Bool}, ab)
    case 0n 1n+q 0n:
      LLogicLogic.pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      LLogicLogic.pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      lsn.lt_le_trans(p, q, r, ab, bc)

def lsn.stop(fit: Bool, less: Bool, -ws: List<&2, C.W>, -node: Nat, -b: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, -rec: C.Line, ef: {fit == False{} : Bool}, el: {less == False{} : Bool}) -> {C.line.next(fit, less, ws, node, b, input, rec) == C.Line{1n, Some{C.line.end(node, b, input)}} : C.Line}:
  match fit less:
    case True{} y:
      LLogicLogic.pc.absurd_tf({C.line.next(True{}, y, ws, node, b, input, rec) == C.Line{1n, Some{C.line.end(node, b, input)}} : C.Line}, ef)
    case False{} True{}:
      LLogicLogic.pc.absurd_tf({C.line.next(False{}, True{}, ws, node, b, input, rec) == C.Line{1n, Some{C.line.end(node, b, input)}} : C.Line}, el)
    case False{} False{}:
      {==}

def lsn.end(+t: Nat, +node: Nat, b: Maybe<&2, List<&2, C.W>>, +bl: Nat, x: List<&2, C.W>, lk: LA.lp.Lk(node, b, bl), +rest: List<&2, C.Reply>, +input: List<&2, C.W>, +longer: {Compactor.not_shorter(b, Compactor.bytes(x)) == True{} : Bool}) -> {C.line.go(1n+t, node, b, bl, C.Says{x} <> rest, input) == C.Line{1n, Some{C.cut(Compactor.or_input(b, input), node)}} : C.Line}:
  match b x:
    case None{} y:
      LLogicLogic.pc.absurd_ft({C.line.go(1n+t, node, None{}, bl, C.Says{y} <> rest, input) == C.Line{1n, Some{C.cut(input, node)}} : C.Line}, longer)
    case Some{+a} Nil{}:
      (eb, eo) = lk
      +z = lsn.lt_le_trans(node, Compactor.bytes(a), 0n, eo, longer)
      LLogicLogic.pc.absurd_ft({C.line.go(1n+t, node, Some{a}, bl, C.Says{Nil{}} <> rest, input) == C.Line{1n, Some{C.cut(a, node)}} : C.Line}, Equal.trans(Bool, False{}, Nat.is_lt(node, 0n), True{}, LNat.pu.lt_zero_f(node), z))
    case Some{+a} +w <> +u:
      (eb, +eo) = lk
      +n = Compactor.bytes(w <> u)
      +len = C.Text.len(w <> u)
      +ef = LA.lp.over(node, w <> u, lsn.lt_le_trans(node, Compactor.bytes(a), n, eo, longer))
      +el0 = lsn.le_not_lt(Compactor.bytes(a), n, longer)
      +el1 = Equal.trans(Bool, Nat.is_lt(len, bl), Nat.is_lt(n, bl), False{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, bl), len, n, LA.lp.len(w <> u)), Equal.trans(Bool, Nat.is_lt(n, bl), Nat.is_lt(n, Compactor.bytes(a)), False{}, Equal.cong(Nat, Bool, z => Nat.is_lt(n, z), bl, Compactor.bytes(a), eb), el0))
      lsn.stop(Nat.is_le(len, node), Nat.is_lt(len, bl), w <> u, node, Some{a}, input, C.line.go(t, node, Some{w <> u}, len, rest, input), ef, el1)

def Compactor.line_stops_when_not_shorter(t, node, input, ps, x, rest, go, longer):
  +g = go
  +k = List.length(&2, C.Reply, ps)
  +b = Compactor.last_said(ps, None{})
  +bl = LA.lp.bl(ps, 0n)
  +y = C.line.go(1n+t, node, b, bl, C.Says{x} <> rest, input)
  +cut = C.cut(Compactor.or_input(b, input), node)
  Equal.trans(C.Line, C.line.go(Nat.add(k, 1n+t), node, None{}, 0n, List.append(&2, C.Reply, ps, C.Says{x} <> rest), input), LA.lp.plus(y, k), C.Line{1n+k, Some{cut}},
    LA.lp.go(ps, 1n+t, node, None{}, 0n, C.Says{x} <> rest, input, Unit{}, g),
    LA.lp.plus_one(y, Some{cut}, k, lsn.end(t, node, b, bl, x, LA.lp.lk(ps, node, None{}, 0n, Unit{}, g), rest, input, longer)))
