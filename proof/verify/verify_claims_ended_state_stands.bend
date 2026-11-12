# eukhe: the proof of LAW verify_claims_ended_state_stands
#
# PROOF: every value of checked and goal; on an ended state each computes to False.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_claims_ended_state_stands(checked, goal):
  match checked:
    case True{}:
      match goal:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}
