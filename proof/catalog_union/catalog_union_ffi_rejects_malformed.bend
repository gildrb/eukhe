# eukhe: the proof of LAW catalog_union_ffi_rejects_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_catalog_union.bend as FCu
import ../../LAWS.bend as Laws

def Laws.catalog_union_ffi_rejects_malformed(s, bad):
  %Equal.sym(Wr.Dec<FCu.Req>, FCu.get_req(s), Wr.Bad{}, bad) : {Laws.wire_opens_err(FCu.answer(_)) == True{} : Bool}
  {==}
