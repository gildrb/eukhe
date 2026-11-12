# eukhe: the proof of LAW verify_claims_unchecked_never
#
# PROOF: not held, no claim, no check: the arms compute to False.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_claims_unchecked_never(goal, ended):
  {==}
