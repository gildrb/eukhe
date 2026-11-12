# eukhe: the proof of LAW verify_claims_goal_claims_itself
#
# PROOF: both values of checked; under an active goal each computes to False.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_claims_goal_claims_itself(checked, ended):
  match checked:
    case True{}:
      {==}
    case False{}:
      {==}
