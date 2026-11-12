# eukhe: the proof of LAW approvals_desk_entry_refused_stays
# PROOF: an open with input is the refused state with its error form; the
# refused state answers every input with the same error form and stays
# refused (by induction on the inputs).

import Base
import ../../bend/ffi_approvals.bend as FAm
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ./base/entry.bend as LAAp

# the refused state's replies: o, then the error form once per input
def rs.feed(ins: List<&2, String>, +o: String) -> {ApprovalsEntry.dk_raw(ins, (FAm.Refused{}, o)) == o <> ApprovalsEntry.dk_refusals(ins) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> +t:
      Equal.cong(List<&2, String>, List<&2, String>, z => o <> z, ApprovalsEntry.dk_raw(t, (FAm.Refused{}, ApprovalsEntry.refused())), ApprovalsEntry.refused() <> ApprovalsEntry.dk_refusals(t), rs.feed(t, ApprovalsEntry.refused()))

def rs.open(s: String, some: {String.is_empty(s) == False{} : Bool}, +ins: List<&2, String>) -> {ApprovalsEntry.dk_raw(ins, FAm.open(s)) == SCon{'E', SCon{' ', "approvals: the open takes no input"}} <> ApprovalsEntry.dk_refusals(ins) : List<&2, String>}:
  match s:
    case SNil{}:
      LAAp.ae.absurd({ApprovalsEntry.dk_raw(ins, FAm.open(SNil{})) == SCon{'E', SCon{' ', "approvals: the open takes no input"}} <> ApprovalsEntry.dk_refusals(ins) : List<&2, String>}, Equal.sym(Bool, True{}, False{}, some))
    case SCon{c, t}:
      rs.feed(ins, SCon{'E', SCon{' ', "approvals: the open takes no input"}})

def ApprovalsEntry.approvals_desk_entry_refused_stays(s, some, ins):
  rs.open(s, some, ins)
