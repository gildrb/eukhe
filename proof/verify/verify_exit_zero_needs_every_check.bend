# eukhe: the proof of LAW verify_exit_zero_needs_every_check
#
# PROOF: not every check holds (LL.vl.holds_around, by induction on the
# checks before), and then the code is 1 or the run's nonzero code
# (LL.vl.exit_nonzero).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_exit_zero_needs_every_check(base, now, pre, s, post, un):
  %LL.vl.holds_around(now, pre, s, post, un) : {Nat.is_eq(V.exit.code(_, base), 0n) == False{} : Bool}
  LL.vl.exit_nonzero(base)
