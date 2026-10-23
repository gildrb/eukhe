# eukhe: the proof of LAW line_empty_is_a_try

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

def pc.line_empty_is_a_try(-t: Nat, -node: Nat, -input: List<&2, C.W>, -rest: List<&2, C.Reply>) -> {C.line(1n+t, node, input, C.Says{Nil{}} <> rest) == C.Line{1n, Some{C.cut(input, node)}} : C.Line}:
  {==}

def Compactor.line_empty_is_a_try(t, node, input, rest):
  pc.line_empty_is_a_try(t, node, input, rest)
