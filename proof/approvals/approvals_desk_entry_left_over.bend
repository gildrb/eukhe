# eukhe: the proof of LAW approvals_desk_entry_left_over
# PROOF: the decoder reads the spelled event back, the rest after it
# untouched (LAAp.ae.rt); the rest is not empty, so the stepper answers the
# error form and keeps the desk.

import Base
import ../../bend/approvals.bend as Am
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ./base/entry.bend as LAAp

def ApprovalsEntry.approvals_desk_entry_left_over(d, e, rest, fits, more):
  %Equal.sym(Wr.Dec<Am.Ev>, FAm.get_ev(ApprovalsEntry.spell_ev(e, rest)), Wr.Got{e, rest}, LAAp.ae.rt(e, rest, fits)) : {FAm.step.ev(d, _) == (FAm.Live{d}, ApprovalsEntry.malformed_event()) : FAm.St & String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FAm.step.end(_, d, e) == (FAm.Live{d}, ApprovalsEntry.malformed_event()) : FAm.St & String}
  {==}
