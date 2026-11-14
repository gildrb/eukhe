# eukhe: the proof of LAW verify_advance_no_checks_ends
#
# PROOF: closed: with no checks none is due, the label is unverified and
# the settling ends at once.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_advance_no_checks_ends(conf, now, cap, rev, tries):
  {==}
