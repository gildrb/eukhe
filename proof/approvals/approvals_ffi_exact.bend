# eukhe: the proof of LAW approvals_ffi_exact
# The call and the spec both answer by whether the input is empty.

import Base
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals/entry.bend as ApprovalsEntry

def afx.end(b: Bool) -> {FAm.ffi.end(b) == ApprovalsEntry.spec.end(b) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ApprovalsEntry.approvals_ffi_exact(s):
  afx.end(Wr.end(s))
