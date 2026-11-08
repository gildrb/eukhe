# eukhe: the proof of LAW seen_entry_answers_spelled
#
# PROOF: the spec's request is the entry's put_req and the spec's verdict
# its put_check (./seen_entry_answers_spelled/spell.bend), so the law is
# seen_entry_refines.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../bend/ffi_doc_seen.bend as Fds
import ../../laws/doc_seen.bend as DocSeen
import ./seen_entry_refines.bend as PSeenEntryRefines
import ./seen_entry_answers_spelled/spell.bend as Ssp

def DocSeen.seen_entry_answers_spelled(ivs, ats, fits):
  +ans = DocSeen.seen.spell_answer(Ds.check(ivs, ats))
  %Ssp.ssp_req(ivs, ats, "") : {Fds.ffi(_) == ans : String}
  %Equal.sym(String, Fds.ffi(Fds.put_req(ivs, ats, "")), Fds.put_check(Ds.check(ivs, ats), ""), PSeenEntryRefines.fsv_entry(ivs, ats, fits)) : {_ == ans : String}
  Ssp.ssp_check(Ds.check(ivs, ats))
