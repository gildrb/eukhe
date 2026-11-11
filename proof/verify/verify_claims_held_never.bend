# eukhe: the proof of LAW verify_claims_held_never
#
# PROOF: the held answer is the first arm of the model: both sides compute to False.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_claims_held_never(checked, goal, claimed, ended):
  {==}
