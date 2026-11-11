# eukhe: the proof of LAW call_lift_unknown_family_untouched
#
# PROOF: no row is named f, so the lookup finds none (cll.fam_none, induction on the table) and the lift answers unknown.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/lookup.bend as LCallLiftLookup

def CallLift.call_lift_unknown_family_untouched(t, f, r, ks, no):
  %Equal.sym(Maybe<&2, Cl.Fam>, Cl.fam_of(t, f), None{}, LCallLiftLookup.cll.fam_none(t, f, no)) : {Cl.lift.fam(r, ks, _) == Cl.Unknown{} : Cl.Lift}
  {==}
