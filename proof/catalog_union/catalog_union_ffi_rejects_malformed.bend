# eukhe: the proof of LAW catalog_union_ffi_rejects_malformed

import Base
import ../../bend/ffi_catalog_union.bend as FCu
import ../../bend/wire.bend as Wr
import ../../laws/catalog_union.bend as CatalogUnion
import ../../laws/base.bend as LawsBase

def CatalogUnion.catalog_union_ffi_rejects_malformed(s, bad):
  %Equal.sym(Wr.Dec<FCu.Req>, FCu.get_req(s), Wr.Bad{}, bad) : {LawsBase.wire_opens_err(FCu.answer(_)) == True{} : Bool}
  {==}
