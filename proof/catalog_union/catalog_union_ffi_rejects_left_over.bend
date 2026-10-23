# eukhe: the proof of LAW catalog_union_ffi_rejects_left_over

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_catalog_union.bend as FCu
import ../../LAWS.bend as Laws

def Laws.catalog_union_ffi_rejects_left_over(s, q, r, got, more):
  %Equal.sym(Wr.Dec<FCu.Req>, FCu.get_req(s), Wr.Got{q, r}, got) : {Laws.wire_opens_err(FCu.answer(_)) == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(r), False{}, more) : {Laws.wire_opens_err(FCu.reply(_, q)) == True{} : Bool}
  {==}
