# eukhe: the proof of LAW child_ffi_exact
# The entry reads every input as the laws' reader does and answers what
# the laws spell (LAE.ct.exact).

import Base
import ../../laws/child/exact.bend as Child
import ./base/entry.bend as LAE

def Child.child_ffi_exact(s):
  LAE.ct.exact(s)
