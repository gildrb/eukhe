# eukhe: the proof of LAW approvals_ffi_answers
# The entry answers as the laws spell; the reader reads back the request
# Rust writes.

import Base
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals.bend as Approvals
import ./base/entry.bend as LAAp

def Approvals.approvals_ffi_answers(q, fits):
  %Equal.sym(String, FAm.ffi(Approvals.spell_req(q, "")), Approvals.spec(Approvals.spell_req(q, "")), LAAp.ap.exact(Approvals.spell_req(q, ""))) : {_ == Approvals.spell_answer(q) : String}
  %Equal.sym(Wr.Dec<FAm.Req>, Approvals.read_req(Approvals.spell_req(q, "")), Wr.Got{q, ""}, LAAp.ap.rt(q, "", fits)) : {Approvals.spec.run(_) == Approvals.spell_answer(q) : String}
  {==}
