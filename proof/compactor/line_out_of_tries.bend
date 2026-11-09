# eukhe: the proof of LAW line_out_of_tries
# Over the replies the line asked again on, line.go takes one call each
# and goes on from the last of them with no try left (LA.lp.go): it ends
# with the best reply held, else the input, cut (LA.lp.end).

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ./base.bend as LA

def Compactor.line_out_of_tries(node, input, ps, rest, go):
  +k = List.length(&2, C.Reply, ps)
  +b = Compactor.last_said(ps, None{})
  +bl = LA.lp.bl(ps, 0n)
  +cut = C.cut(Compactor.or_input(b, input), node)
  %LA.lp.add_zero(k) : {C.line(_, node, input, List.append(&2, C.Reply, ps, rest)) == C.Line{_, Some{cut}} : C.Line}
  Equal.trans(C.Line, C.line.go(Nat.add(k, 0n), node, None{}, 0n, List.append(&2, C.Reply, ps, rest), input), LA.lp.plus(C.line.go(0n, node, b, bl, rest, input), k), C.Line{Nat.add(k, 0n), Some{cut}},
    LA.lp.go(ps, 0n, node, None{}, 0n, rest, input, Unit{}, go),
    Equal.cong(List<&2, C.W>, C.Line, z => C.Line{Nat.add(k, 0n), Some{z}}, C.line.end(node, b, input), cut, LA.lp.end(node, b, input)))
