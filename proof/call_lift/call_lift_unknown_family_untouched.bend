# eukhe: the proof of LAW call_lift_unknown_family_untouched
#
# PROOF: the lift is the spec's (call_lift_refines_spec); the spec looks up the family's current rev, which the premise says is none, so it answers unknown.

import Base
import ../../bend/call_lift.bend as Cl
import ../../spec/harness/lift.bend as Sp
import ../../laws/call_lift.bend as CallLift
import ./call_lift_refines_spec.bend as PCallLiftRefinesSpec

def CallLift.call_lift_unknown_family_untouched(t, f, r, ks, no):
  %Equal.sym(Cl.Lift, Cl.lift(t, Cl.Call{f, r, ks}), Sp.lift_spec(t, Cl.Call{f, r, ks}), CallLift.call_lift_refines_spec(t, Cl.Call{f, r, ks})) : {_ == Cl.Unknown{} : Cl.Lift}
  %Equal.sym(Maybe<&2, String>, Sp.current(t, f), None{}, no) : {Sp.lift_spec.cur(r, ks, _, Sp.steps_of(t, f)) == Cl.Unknown{} : Cl.Lift}
  {==}
