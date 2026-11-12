# eukhe: the proof of LAW verify_command_expected_exit_confirms
#
# PROOF: the command's code is the expected one (LL.vl.eq_refl), so the exit
# confirms.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_command_expected_exit_confirms(e):
  %LL.vl.eq_refl(e) : {V.grade_exit(_) == V.Confirmed{} : V.Verdict}
  {==}
