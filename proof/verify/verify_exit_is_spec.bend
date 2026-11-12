# eukhe: the proof of LAW verify_exit_is_spec
#
# PROOF: every check holds exactly when as many are confirmed as there are
# (LL.vl.holds); then the cases of that and of the run's code (LL.vl.exit).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_exit_is_spec(base, now, slots):
  %LL.vl.holds(now, slots) : {V.exit.code(_, base) == S.exit(base, now, slots) : Nat}
  LL.vl.exit(S.all_confirmed(now, slots), base)
