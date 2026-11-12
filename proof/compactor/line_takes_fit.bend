# eukhe: the proof of LAW line_takes_fit
# Over the replies the line asked again on, line.go takes one call each
# and goes on from the last of them (LA.lp.go); then a reply of 1 to node
# bytes (its Text.len is its bytes, LA.lp.len) is the line, whole.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LA

def ltf.take(fit: Bool, less: Bool, -ws: List<&2, C.W>, -node: Nat, -b: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, -rec: C.Line, ef: {fit == True{} : Bool}) -> {C.line.next(fit, less, ws, node, b, input, rec) == C.Line{1n, Some{ws}} : C.Line}:
  match fit less:
    case True{} y:
      {==}
    case False{} y:
      LLogicLogic.pc.absurd_ft({C.line.next(False{}, y, ws, node, b, input, rec) == C.Line{1n, Some{ws}} : C.Line}, ef)

def ltf.end(+t: Nat, +node: Nat, +b: Maybe<&2, List<&2, C.W>>, +bl: Nat, f: List<&2, C.W>, +rest: List<&2, C.Reply>, +input: List<&2, C.W>, fit: {Bool.and(Nat.is_lt(0n, Compactor.bytes(f)), Nat.is_le(Compactor.bytes(f), node)) == True{} : Bool}) -> {C.line.go(1n+t, node, b, bl, C.Says{f} <> rest, input) == C.Line{1n, Some{f}} : C.Line}:
  match f:
    case Nil{}:
      LLogicLogic.pc.absurd_ft({C.line.go(1n+t, node, b, bl, C.Says{Nil{}} <> rest, input) == C.Line{1n, Some{Nil{}}} : C.Line}, fit)
    case +w <> +u:
      +n = Compactor.bytes(w <> u)
      +le = LLogicBool.wr_and_r(Nat.is_lt(0n, n), Nat.is_le(n, node), fit)
      +ef = Equal.trans(Bool, Nat.is_le(C.Text.len(w <> u), node), Nat.is_le(n, node), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, node), C.Text.len(w <> u), n, LA.lp.len(w <> u)), le)
      ltf.take(Nat.is_le(C.Text.len(w <> u), node), C.shorter(C.Text.len(w <> u), b, bl), w <> u, node, b, input, C.line.go(t, node, Some{w <> u}, C.Text.len(w <> u), rest, input), ef)

def Compactor.line_takes_fit(t, node, input, ps, f, rest, go, fit):
  +k = List.length(&2, C.Reply, ps)
  +b = Compactor.last_said(ps, None{})
  +bl = LA.lp.bl(ps, 0n)
  +x = C.line.go(1n+t, node, b, bl, C.Says{f} <> rest, input)
  Equal.trans(C.Line, C.line.go(Nat.add(k, 1n+t), node, None{}, 0n, List.append(&2, C.Reply, ps, C.Says{f} <> rest), input), LA.lp.plus(x, k), C.Line{1n+k, Some{f}},
    LA.lp.go(ps, 1n+t, node, None{}, 0n, C.Says{f} <> rest, input, Unit{}, go),
    LA.lp.plus_one(x, Some{f}, k, ltf.end(t, node, b, bl, f, rest, input, fit)))
