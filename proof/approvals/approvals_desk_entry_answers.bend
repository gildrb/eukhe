# eukhe: the proof of LAW approvals_desk_entry_answers
# PROOF: the decoder reads the spelled event back whole, nothing after it
# (LAAp.ae.rt, approvals_desk_entry_reads); the stepper then answers the
# model's step, spelled (LAAp.ae.next, LAAp.ae.step_reply).

import Base
import ../../bend/approvals.bend as Am
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ./base/entry.bend as LAAp

def ApprovalsEntry.approvals_desk_entry_answers(d, e, h):
  %Equal.sym(Wr.Dec<Am.Ev>, FAm.get_ev(ApprovalsEntry.spell_ev(e, "")), Wr.Got{e, ""}, LAAp.ae.rt(e, "", h)) : {FAm.step.ev(d, _) == ApprovalsEntry.dk_reply(e, ApprovalsEntry.dk_next(d), Am.dstep(d, e)) : FAm.St & String}
  %LAAp.ae.next(d) : {FAm.step.reply(e, FAm.D.next(d), Am.dstep(d, e)) == ApprovalsEntry.dk_reply(e, _, Am.dstep(d, e)) : FAm.St & String}
  LAAp.ae.step_reply(e, FAm.D.next(d), Am.dstep(d, e))
