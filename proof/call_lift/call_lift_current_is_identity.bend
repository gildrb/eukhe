# eukhe: the proof of LAW call_lift_current_is_identity
#
# PROOF: the lift is the spec's (call_lift_refines_spec); the spec finds the family's current rev, which the premise says is the call's own rev r, and String.eq(r, r) holds (clm.str_refl), so it answers current.

import Base
import ../../bend/call_lift.bend as Cl
import ../../spec/harness/lift.bend as Sp
import ../../laws/call_lift.bend as CallLift
import ./base/string.bend as LCallLiftString
import ./call_lift_refines_spec.bend as PCallLiftRefinesSpec

def CallLift.call_lift_current_is_identity(t, f, r, ks, cur):
  %Equal.sym(Cl.Lift, Cl.lift(t, Cl.Call{f, r, ks}), Sp.lift_spec(t, Cl.Call{f, r, ks}), CallLift.call_lift_refines_spec(t, Cl.Call{f, r, ks})) : {_ == Cl.Current{} : Cl.Lift}
  %Equal.sym(Maybe<&2, String>, Sp.current(t, f), Some{r}, cur) : {Sp.lift_spec.cur(r, ks, _, Sp.steps_of(t, f)) == Cl.Current{} : Cl.Lift}
  %LCallLiftString.clm.str_refl_sym(r) : {Sp.lift_spec.at(_, r, ks, Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), r, Sp.next(Sp.steps_of(t, f), r))) == Cl.Current{} : Cl.Lift}
  {==}
