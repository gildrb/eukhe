# eukhe: the proof of LAW verify_record_old_revision_refused
#
# PROOF: the verifier's Record reads whether its revision is the current
# one: by the premise it is not, and the refusal computes.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_record_old_revision_refused(of, i, v, at, rev, slots, claimed, tries, old):
  %old : {V.act(V.Verifier{}, V.Record{of, i, v, at}, V.Acc{rev, slots, claimed, tries}) == V.act.stamp(_, i, V.Judged{v, at}, rev, slots, claimed, tries) : Bool & V.Acc}
  {==}
