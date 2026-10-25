# eukhe: the proof of LAW approvals_desk_entry_answers
# The step is the spec's (approvals_desk_entry_exact), and the spec reads
# the spelled event back whole (approvals_desk_entry_reads).

import Base
import ../../bend/approvals.bend as Am
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ./base/entry.bend as LAAp

def ApprovalsEntry.approvals_desk_entry_answers(d, e, h):
  %Equal.sym(FAm.St & String, FAm.step(FAm.Live{d}, ApprovalsEntry.spell_ev(e, "")), ApprovalsEntry.dspec(d, ApprovalsEntry.spell_ev(e, "")), LAAp.ae.exact(d, ApprovalsEntry.spell_ev(e, ""))) : {_ == ApprovalsEntry.dk_reply(e, ApprovalsEntry.dk_next(d), Am.dstep(d, e)) : FAm.St & String}
  %Equal.sym(Wr.Dec<Am.Ev>, ApprovalsEntry.read_ev(ApprovalsEntry.spell_ev(e, "")), Wr.Got{e, ""}, LAAp.ae.rt(e, "", h)) : {ApprovalsEntry.dspec.run(d, _) == ApprovalsEntry.dk_reply(e, ApprovalsEntry.dk_next(d), Am.dstep(d, e)) : FAm.St & String}
  {==}
