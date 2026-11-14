# eukhe: the proof of LAW verify_unconfirmed_check_never_verified
#
# PROOF: there is a check (LL.vl.some_around) and not every check holds
# (LL.vl.holds_around, by induction on the checks before), so the label
# is failed or unverified (LL.vl.unheld), whatever confinement says.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_unconfirmed_check_never_verified(conf, now, pre, s, post, un):
  %LL.vl.some_around(pre, s, post) : {Verify.sp_succeeds(V.label.of(conf, V.refuted(now, Verify.sp_around(pre, s, post)), Bool.and(_, V.holds(now, Verify.sp_around(pre, s, post))))) == False{} : Bool}
  %LL.vl.holds_around(now, pre, s, post, un) : {Verify.sp_succeeds(V.label.of(conf, V.refuted(now, Verify.sp_around(pre, s, post)), _)) == False{} : Bool}
  LL.vl.unheld(conf, V.refuted(now, Verify.sp_around(pre, s, post)))
