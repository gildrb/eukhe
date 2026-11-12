# eukhe: the proof of LAW verify_claim_keeps_verdicts
#
# PROOF: a Claim never reads the actor: both sides compute to the same
# term.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_claim_keeps_verdicts(who, rev, slots, claimed, tries):
  {==}
