# eukhe: the proof of LAW call_lift_rename_clashes
#
# PROOF: has is "the names do not lack k" (cll.has_is), so the premises make both tests true, and the op appends the clashed receipt and moves nothing.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/args.bend as LCallLiftArgs

def CallLift.call_lift_rename_clashes(args, from, to, rs, present, taken):
  %Equal.sym(Bool, Cl.has(args, from), True{}, LCallLiftArgs.cll.has_is(args, from, False{}, present)) : {Cl.apply_op.rename(_, Cl.has(args, to), from, to, args, rs) == Cl.St{args, List.append(&2, Cl.Receipt, rs, [Cl.Clashed{from, to}])} : Cl.St}
  %Equal.sym(Bool, Cl.has(args, to), True{}, LCallLiftArgs.cll.has_is(args, to, False{}, taken)) : {Cl.apply_op.rename(True{}, _, from, to, args, rs) == Cl.St{args, List.append(&2, Cl.Receipt, rs, [Cl.Clashed{from, to}])} : Cl.St}
  {==}
