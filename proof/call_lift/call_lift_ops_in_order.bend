# eukhe: the proof of LAW call_lift_ops_in_order
#
# PROOF: no ops and one op compute; the append by induction on os1 (cll.ops_append): the first op of os1 applies first on both sides, then the induction hypothesis.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift

def cll.ops_append(+os1: List<&2, Cl.Op>, +os2: List<&2, Cl.Op>, +st: Cl.St) -> {Cl.apply_ops(List.append(&2, Cl.Op, os1, os2), st) == Cl.apply_ops(os2, Cl.apply_ops(os1, st)) : Cl.St}:
  match os1:
    case Nil{}:
      {==}
    case Con{+o, rest}:
      cll.ops_append(rest, os2, Cl.apply_op(o, st))

def CallLift.call_lift_ops_in_order(os1, os2, o, st):
  ({==}, ({==}, cll.ops_append(os1, os2, st)))
