# eukhe: the proof of LAW line_error_fails

import Base
import ../../bend/compactor.bend as C
import ../../LAWS.bend as Laws

def pc.line_error_fails(-t: Nat, -node: Nat, -input: List<&2, C.W>, -rest: List<&2, C.Reply>) -> {C.line(1n+t, node, input, C.Erred{} <> rest) == C.Line{1n, None{}} : C.Line}:
  {==}

def Laws.line_error_fails(t, node, input, rest):
  pc.line_error_fails(t, node, input, rest)
