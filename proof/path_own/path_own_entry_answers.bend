# eukhe: the proof of LAW path_own_entry_answers
#
# PROOF: the entry's decoder reads back the request Rust writes
# (LA.po.rt), and its reply encoder is the laws' spelling (LA.po.reply).

import Base
import ../../bend/ffi_path_own.bend as FPo
import ../../bend/wire.bend as Wr
import ../../laws/path_own.bend as PathOwn
import ./base.bend as LA

def PathOwn.path_own_entry_answers(q, fits):
  %Equal.sym(Wr.Dec<FPo.Req>, FPo.get_req(PathOwn.sp_po_req(q, "")), Wr.Got{q, ""}, LA.po.rt(q, "", fits)) : {FPo.run(_) == PathOwn.sp_po_reply(q) : String}
  LA.po.reply(q)
