# eukhe: the proof of LAW verify_command_other_exit_refutes
#
# PROOF: rewrite the comparison of the codes with the premise; the exit
# refutes.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_command_other_exit_refutes(e, c, other):
  %Equal.sym(Bool, Nat.is_eq(c, e), False{}, other) : {V.grade_exit(_) == V.Refuted{} : V.Verdict}
  {==}
