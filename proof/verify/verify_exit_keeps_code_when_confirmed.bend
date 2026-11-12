# eukhe: the proof of LAW verify_exit_keeps_code_when_confirmed
#
# PROOF: the confirmations all hold (LL.vl.pass_holds, by induction on their
# number), so the run's code is kept.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_exit_keeps_code_when_confirmed(base, now, n):
  %LL.vl.pass_holds(now, n) : {V.exit.code(_, base) == base : Nat}
  {==}
