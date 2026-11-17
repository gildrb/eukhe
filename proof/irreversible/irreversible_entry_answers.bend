# eukhe: the proof of LAW irreversible_entry_answers
#
# PROOF: the entry's decoder reads back the request Rust writes
# (LA.irb.rt), and its reply encoder is the laws' spelling (LA.irb.reply).

import Base
import ../../bend/ffi_irreversible.bend as FIr
import ../../bend/wire.bend as Wr
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

def Irreversible.irreversible_entry_answers(q, fits):
  %Equal.sym(Wr.Dec<FIr.Req>, FIr.get_req(Irreversible.sp_ir_req(q, "")), Wr.Got{q, ""}, LA.irb.rt(q, "", fits)) : {FIr.run(_) == Irreversible.sp_ir_reply(q) : String}
  LA.irb.reply(q)
