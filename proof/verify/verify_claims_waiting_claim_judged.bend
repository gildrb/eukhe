# eukhe: the proof of LAW verify_claims_waiting_claim_judged
#
# PROOF: not held, then a waiting claim is the first arm: both sides compute to True.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_claims_waiting_claim_judged(checked, goal, ended):
  {==}
