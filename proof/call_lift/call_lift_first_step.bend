# eukhe: the proof of LAW call_lift_first_step
#
# PROOF: induction on pre (cll.step_found): a step of pre leaves another rev (the premise), so step_of goes past it; at the step leaving x, String.eq(x, x) holds (clm.str_refl) and step_of answers it.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/lookup.bend as LCallLiftLookup

def CallLift.call_lift_first_step(pre, post, x, b, o, before):
  LCallLiftLookup.cll.step_found(pre, post, x, b, o, before)
