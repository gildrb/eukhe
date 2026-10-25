# eukhe: the proof of LAW approvals_desk_entry_history
# The open is the empty desk; then by induction on the events, each
# spelled event moves the entry as the model's step does and answers its
# spelled reply (approvals_desk_entry_answers), so the next state is the
# model's desk after it and the rest follows.

import Base
import ../../bend/approvals.bend as Am
import ../../bend/ffi_approvals.bend as FAm
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ./approvals_desk_entry_answers.bend as PApprovalsDeskEntryAnswers
import ./base/entry.bend as LAAp

def adh.step(t: List<&2, Am.Ev>, +e: Am.Ev, +n: Nat, r: Am.D & List<&2, Am.Act>, ih: @d2: Am.D -> @o2: String -> {ApprovalsEntry.dk_feed(t, (FAm.Live{d2}, o2)) == o2 <> ApprovalsEntry.dk_replies(t, d2) : List<&2, String>}) -> {ApprovalsEntry.dk_feed(t, ApprovalsEntry.dk_reply(e, n, r)) == ApprovalsEntry.spell_reply(e, n, ApprovalsEntry.dk_acts(r)) <> ApprovalsEntry.dk_replies(t, ApprovalsEntry.dk_desk(r)) : List<&2, String>}:
  (d2, as) = r
  ih(d2, ApprovalsEntry.spell_reply(e, n, as))

def adh.go(es: List<&2, Am.Ev>, +d: Am.D, out: String, fits: {ApprovalsEntry.evs_fit(es) == True{} : Bool}) -> {ApprovalsEntry.dk_feed(es, (FAm.Live{d}, out)) == out <> ApprovalsEntry.dk_replies(es, d) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +t:
      +f2 = fits
      %Equal.sym(FAm.St & String, FAm.step(FAm.Live{d}, ApprovalsEntry.spell_ev(e, "")), ApprovalsEntry.dk_reply(e, ApprovalsEntry.dk_next(d), Am.dstep(d, e)), ApprovalsEntry.approvals_desk_entry_answers(d, e, LAAp.ae.and_l(ApprovalsEntry.ev_fits(e), ApprovalsEntry.evs_fit(t), f2))) : {out <> ApprovalsEntry.dk_feed(t, _) == out <> ApprovalsEntry.dk_replies(e <> t, d) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => out <> z, ApprovalsEntry.dk_feed(t, ApprovalsEntry.dk_reply(e, ApprovalsEntry.dk_next(d), Am.dstep(d, e))), ApprovalsEntry.dk_replies(e <> t, d), adh.step(t, e, ApprovalsEntry.dk_next(d), Am.dstep(d, e), d2 => o2 => adh.go(t, d2, o2, LAAp.ae.and_r(ApprovalsEntry.ev_fits(e), ApprovalsEntry.evs_fit(t), f2))))

def ApprovalsEntry.approvals_desk_entry_history(es, fits):
  adh.go(es, Am.D{0n, Nil{}}, "", fits)
