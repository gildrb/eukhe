# eukhe: the proof of LAW verify_assign_too_many_refused
#
# PROOF: the owner's Assign reads whether n is at most max_checks: by the
# premise it is not, and the refusal computes.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_assign_too_many_refused(n, a, many):
  %many : {V.act(V.Owner{}, V.Assign{n}, a) == V.act.assign.fits(_, n, a) : Bool & V.Acc}
  {==}
