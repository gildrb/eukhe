# eukhe: the proof of LAW line_empty_is_a_try
# Over the replies the line asked again on, line.go takes one call each
# and goes on from the last of them (LA.lp.go); then an empty reply ends
# the next call with the best reply held, else the input, cut (LA.lp.end).

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ./base.bend as LA

def Compactor.line_empty_is_a_try(t, node, input, ps, rest, go):
  +k = List.length(&2, C.Reply, ps)
  +b = Compactor.last_said(ps, None{})
  +bl = LA.lp.bl(ps, 0n)
  +x = C.line.go(1n+t, node, b, bl, C.Says{Nil{}} <> rest, input)
  +cut = C.cut(Compactor.or_input(b, input), node)
  Equal.trans(C.Line, C.line.go(Nat.add(k, 1n+t), node, None{}, 0n, List.append(&2, C.Reply, ps, C.Says{Nil{}} <> rest), input), LA.lp.plus(x, k), C.Line{1n+k, Some{cut}},
    LA.lp.go(ps, 1n+t, node, None{}, 0n, C.Says{Nil{}} <> rest, input, Unit{}, go),
    LA.lp.plus_one(x, Some{cut}, k, Equal.cong(List<&2, C.W>, C.Line, z => C.Line{1n, Some{z}}, C.line.end(node, b, input), cut, LA.lp.end(node, b, input))))
