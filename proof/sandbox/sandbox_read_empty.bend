# eukhe: the proof of LAW sandbox_read_empty
#
# PROOF: an empty workspace reads None by evaluation.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def Sandbox.sandbox_read_empty(p):
  {==}
