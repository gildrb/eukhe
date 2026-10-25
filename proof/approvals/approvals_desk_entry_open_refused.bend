# eukhe: the proof of LAW approvals_desk_entry_open_refused
# The input is not empty, so it is not the whole open (wire_end_exact).

import Base
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact

def ApprovalsEntry.approvals_desk_entry_open_refused(s, h):
  %Wire.wire_end_exact(s) : {FAm.open.end(_) == (FAm.Refused{}, SCon{'E', SCon{' ', "approvals: the open takes no input"}}) : FAm.St & String}
  %Equal.sym(Bool, String.is_empty(s), False{}, h) : {FAm.open.end(_) == (FAm.Refused{}, SCon{'E', SCon{' ', "approvals: the open takes no input"}}) : FAm.St & String}
  {==}
