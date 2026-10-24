# eukhe: the proof of LAW approvals_ffi_exact
# The entry reads every input as the laws' reader does and answers what
# the laws spell (LAAp.ap.exact).

import Base
import ../../laws/approvals.bend as Approvals
import ./base/entry.bend as LAAp

def Approvals.approvals_ffi_exact(s):
  LAAp.ap.exact(s)
