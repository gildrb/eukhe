# eukhe: the proof of LAW verify_advance_rests_unclaimed
#
# PROOF: without a claim the step never reads the slots: both sides compute
# to the same term.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_advance_rests_unclaimed(now, cap, rev, slots, tries):
  {==}
