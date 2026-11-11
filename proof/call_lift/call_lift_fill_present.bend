# eukhe: the proof of LAW call_lift_fill_present
#
# PROOF: has is "the names do not lack k" (cll.has_is), so the premise makes the test true, and the op leaves the arguments and receipts.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/args.bend as LCallLiftArgs

def CallLift.call_lift_fill_present(args, key, json, rs, present):
  %Equal.sym(Bool, Cl.has(args, key), True{}, LCallLiftArgs.cll.has_is(args, key, False{}, present)) : {Cl.apply_op.fill(_, key, json, args, rs) == Cl.St{args, rs} : Cl.St}
  {==}
