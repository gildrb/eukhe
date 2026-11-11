# eukhe: the proof of LAW approvals_ffi_left_over
# The input is not empty, so it is not the whole call (Wr.end is String.is_empty).

import Base
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals/entry.bend as ApprovalsEntry

def ApprovalsEntry.approvals_ffi_left_over(more, some):
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {FAm.ffi.end(_) == ApprovalsEntry.malformed() : String}
  {==}
