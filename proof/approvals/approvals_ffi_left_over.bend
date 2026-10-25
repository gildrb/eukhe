# eukhe: the proof of LAW approvals_ffi_left_over
# The input is not empty, so it is not the whole call (wire_end_exact).

import Base
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact

def ApprovalsEntry.approvals_ffi_left_over(more, some):
  %Wire.wire_end_exact(more) : {FAm.ffi.end(_) == ApprovalsEntry.malformed() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {FAm.ffi.end(_) == ApprovalsEntry.malformed() : String}
  {==}
