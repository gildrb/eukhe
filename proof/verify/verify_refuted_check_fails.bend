# eukhe: the proof of LAW verify_refuted_check_fails
#
# PROOF: some check is refuted (LL.vl.refuted_around, by induction on the
# checks before), and the label reads that first.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_refuted_check_fails(now, pre, post):
  %LL.vl.refuted_around(now, pre, post) : {V.label.of(_, Bool.and(V.some(Verify.sp_around(pre, V.Judged{V.Refuted{}, now}, post)), V.holds(now, Verify.sp_around(pre, V.Judged{V.Refuted{}, now}, post)))) == V.Failed{} : V.Label}
  {==}
