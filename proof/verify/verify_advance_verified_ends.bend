# eukhe: the proof of LAW verify_advance_verified_ends
#
# PROOF: LA.va.advance_ok: the label settles the claim with itself
# (LA.va.settle_ok); a spec label that reports every check confirmed has
# every check confirmed on the state now, so none is due (LA.va.ok_none);
# the label is the spec's (LAW verify_label_is_spec).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA
import ./verify_label_is_spec.bend as PLabel

def Verify.verify_advance_verified_ends(conf, now, cap, rev, slots, tries, l, ok, all):
  LA.va.advance_ok(conf, now, cap, rev, slots, tries, l, ok, all, Verify.verify_label_is_spec(conf, now, slots))
