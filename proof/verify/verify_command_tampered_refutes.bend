# eukhe: the proof of LAW verify_command_tampered_refutes
#
# PROOF: both sides compute: the protected files are read first.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_command_tampered_refutes(e, ev):
  {==}
