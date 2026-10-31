# eukhe: the proof of LAW call_lift_replay_byte_stable
#
# PROOF: induction on xs: no first part spells as the rest alone; a first call spells its own lift, then (the induction hypothesis) the lifts of the rest of the first part, then those of ys.

import Base
import ../../bend/call_lift.bend as Cl
import ../../bend/ffi_call_lift.bend as FCl
import ../../laws/call_lift.bend as CallLift

def CallLift.call_lift_replay_byte_stable(t, xs, ys, rest):
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +more}:
      %CallLift.call_lift_replay_byte_stable(t, more, ys, rest) : {FCl.put_lift(Cl.lift(t, c), FCl.put_lifts(t, List.append(&2, Cl.Call, more, ys), rest)) == FCl.put_lift(Cl.lift(t, c), _) : String}
      {==}
