# eukhe: the proof of LAW verify_advance_verified_ends
#
# PROOF: LA.va.advance_verified: a verified spec label has every check
# confirmed on the state now, so none is due (LA.va.verified_none); the
# label is the spec's (LAW verify_label_is_spec) and settles verified.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA
import ./verify_label_is_spec.bend as PLabel

def Verify.verify_advance_verified_ends(now, cap, rev, slots, tries, all):
  LA.va.advance_verified(now, cap, rev, slots, tries, all, Verify.verify_label_is_spec(now, slots))
