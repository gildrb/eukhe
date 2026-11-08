# eukhe: the proof of LAW restart_ffi_exact_spec
# The entry reads every input as the laws' reader does and answers what
# the laws spell (LAE.rse.exact).

import Base
import ../../laws/supervise.bend as Supervise
import ./base/entry.bend as LAE

def Supervise.restart_ffi_exact_spec(s):
  LAE.rse.exact(s)
