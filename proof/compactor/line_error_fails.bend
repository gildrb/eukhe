# eukhe: the proof of LAW line_error_fails
# Over the replies the line asked again on, line.go takes one call each
# and goes on from the last of them (LA.lp.go); then a provider error or
# no reply ends the next call failed (lef.end).

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def lef.end(-t: Nat, -node: Nat, -b: Maybe<&2, List<&2, C.W>>, -bl: Nat, rest: List<&2, C.Reply>, -input: List<&2, C.W>, none: {Compactor.fails_next(rest) == True{} : Bool}) -> {C.line.go(1n+t, node, b, bl, rest, input) == C.Line{1n, None{}} : C.Line}:
  match rest:
    case Nil{}:
      {==}
    case r <> more:
      match r:
        case C.Erred{}:
          {==}
        case C.Says{ws}:
          LLogicLogic.pc.absurd_ft({C.line.go(1n+t, node, b, bl, C.Says{ws} <> more, input) == C.Line{1n, None{}} : C.Line}, none)

def Compactor.line_error_fails(t, node, input, ps, rest, go, none):
  +k = List.length(&2, C.Reply, ps)
  +b = Compactor.last_said(ps, None{})
  +bl = LA.lp.bl(ps, 0n)
  Equal.trans(C.Line, C.line.go(Nat.add(k, 1n+t), node, None{}, 0n, List.append(&2, C.Reply, ps, rest), input), LA.lp.plus(C.line.go(1n+t, node, b, bl, rest, input), k), C.Line{1n+k, None{}},
    LA.lp.go(ps, 1n+t, node, None{}, 0n, rest, input, Unit{}, go),
    LA.lp.plus_one(C.line.go(1n+t, node, b, bl, rest, input), None{}, k, lef.end(t, node, b, bl, rest, input, none)))
