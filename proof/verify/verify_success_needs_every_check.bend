# eukhe: the proof of LAW verify_success_needs_every_check
#
# PROOF: case on the claim, on what is due and on the label
# (LA.va.go_said): every step but the settling of a verified label refutes
# the premise; the label is the spec's (LAW verify_label_is_spec).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA
import ./verify_label_is_spec.bend as PLabel

def Verify.verify_success_needs_every_check(now, cap, a, said):
  match a:
    case V.Acc{rev, slots, claimed, tries}:
      match claimed:
        case True{}:
          LA.va.go_said(V.due(now, slots, 0n), now, cap, rev, slots, tries, said, Verify.verify_label_is_spec(now, slots))
        case False{}:
          LA.va.absurd_rest({S.label(now, slots) == V.Verified{} : V.Label}, said)
