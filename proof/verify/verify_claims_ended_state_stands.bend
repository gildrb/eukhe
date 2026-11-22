# eukhe: the proof of LAW verify_claims_ended_state_stands
#
# PROOF: every value of checked; on an ended state each computes to False.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_claims_ended_state_stands(checked):
  match checked:
    case True{}:
      {==}
    case False{}:
      {==}
