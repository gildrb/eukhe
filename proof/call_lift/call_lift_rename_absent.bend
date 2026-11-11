# eukhe: the proof of LAW call_lift_rename_absent
#
# PROOF: has is "the names do not lack k" (cll.has_is), so the premise makes the test false, and the op leaves the arguments and receipts.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/args.bend as LCallLiftArgs

def CallLift.call_lift_rename_absent(args, from, to, rs, absent):
  %Equal.sym(Bool, Cl.has(args, from), False{}, LCallLiftArgs.cll.has_is(args, from, True{}, absent)) : {Cl.apply_op.rename(_, Cl.has(args, to), from, to, args, rs) == Cl.St{args, rs} : Cl.St}
  {==}
