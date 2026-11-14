# eukhe: the proof of LAW verify_all_confirmed_verifies
#
# PROOF: the confirmations refute nothing (LL.vl.pass_unrefuted) and all
# hold (LL.vl.pass_holds), by induction on their number; there is one;
# programs run confined.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_all_confirmed_verifies(now, n):
  %LL.vl.pass_unrefuted(now, 1n+n) : {V.label.of(True{}, _, Bool.and(True{}, V.holds(now, Verify.sp_all_pass(1n+n, now)))) == V.Verified{} : V.Label}
  %LL.vl.pass_holds(now, 1n+n) : {V.label.of(True{}, False{}, _) == V.Verified{} : V.Label}
  {==}
