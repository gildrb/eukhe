# eukhe: the proof of LAW call_lift_current_is_identity
#
# PROOF: the lookup finds the family (cll.fam_found: the rows before it are named otherwise), whose current rev is the call's own rev r; String.eq(r, r) holds (clm.str_refl), so the lift answers current.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/string.bend as LCallLiftString
import ./base/lookup.bend as LCallLiftLookup

def CallLift.call_lift_current_is_identity(pre, post, f, r, ss, ks, first):
  %Equal.sym(Maybe<&2, Cl.Fam>, Cl.fam_of(List.append(&2, Cl.Fam, pre, Cl.Fam{f, r, ss} <> post), f), Some{Cl.Fam{f, r, ss}}, LCallLiftLookup.cll.fam_found(pre, post, f, r, ss, first)) : {Cl.lift.fam(r, ks, _) == Cl.Current{} : Cl.Lift}
  %LCallLiftString.clm.str_refl_sym(r) : {Cl.lift.at(_, r, ks, Cl.walk(List.length(&2, Cl.Step, ss), ss, r, Cl.step_of(ss, r))) == Cl.Current{} : Cl.Lift}
  {==}
