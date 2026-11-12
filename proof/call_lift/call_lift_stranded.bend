# eukhe: the proof of LAW call_lift_stranded
#
# PROOF: the lookup finds the family (cll.fam_found); the call is not at its current rev (the premise), no step leaves its rev (cll.step_none), and a walk with no step is none at every fuel (cll.walk_none), so the lift answers stranded.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/lookup.bend as LCallLiftLookup

def CallLift.call_lift_stranded(pre, post, f, cur, ss, r, ks, first, old, none):
  %Equal.sym(Maybe<&2, Cl.Fam>, Cl.fam_of(List.append(&2, Cl.Fam, pre, Cl.Fam{f, cur, ss} <> post), f), Some{Cl.Fam{f, cur, ss}}, LCallLiftLookup.cll.fam_found(pre, post, f, cur, ss, first)) : {Cl.lift.fam(r, ks, _) == Cl.Stranded{} : Cl.Lift}
  %Equal.sym(Bool, String.eq(r, cur), False{}, old) : {Cl.lift.at(_, cur, ks, Cl.walk(List.length(&2, Cl.Step, ss), ss, cur, Cl.step_of(ss, r))) == Cl.Stranded{} : Cl.Lift}
  %Equal.sym(Maybe<&2, Cl.Step>, Cl.step_of(ss, r), None{}, LCallLiftLookup.cll.step_none(ss, r, none)) : {Cl.lift.path(cur, ks, Cl.walk(List.length(&2, Cl.Step, ss), ss, cur, _)) == Cl.Stranded{} : Cl.Lift}
  %Equal.sym(Maybe<&2, List<&2, Cl.Op>>, Cl.walk(List.length(&2, Cl.Step, ss), ss, cur, None{}), None{}, LCallLiftLookup.cll.walk_none(List.length(&2, Cl.Step, ss), ss, cur)) : {Cl.lift.path(cur, ks, _) == Cl.Stranded{} : Cl.Lift}
  {==}
