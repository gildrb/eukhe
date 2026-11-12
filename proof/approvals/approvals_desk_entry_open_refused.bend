# eukhe: the proof of LAW approvals_desk_entry_open_refused
# The input is not empty, so it is not the whole open (Wr.end is String.is_empty).

import Base
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals/entry.bend as ApprovalsEntry

def ApprovalsEntry.approvals_desk_entry_open_refused(s, h):
  %Equal.sym(Bool, String.is_empty(s), False{}, h) : {FAm.open.end(_) == (FAm.Refused{}, SCon{'E', SCon{' ', "approvals: the open takes no input"}}) : FAm.St & String}
  {==}
