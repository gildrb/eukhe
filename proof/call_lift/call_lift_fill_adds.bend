# eukhe: the proof of LAW call_lift_fill_adds
#
# PROOF: has is "the names do not lack k" (cll.has_is), so the premise makes the test false, and the op appends the added argument and the filled receipt.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/args.bend as LCallLiftArgs

def CallLift.call_lift_fill_adds(args, key, json, rs, absent):
  %Equal.sym(Bool, Cl.has(args, key), False{}, LCallLiftArgs.cll.has_is(args, key, True{}, absent)) : {Cl.apply_op.fill(_, key, json, args, rs) == Cl.St{List.append(&2, Cl.Arg, args, [Cl.Added{key, json}]), List.append(&2, Cl.Receipt, rs, [Cl.Filled{key}])} : Cl.St}
  {==}
