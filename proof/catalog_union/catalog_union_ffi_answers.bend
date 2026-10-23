# eukhe: the proof of LAW catalog_union_ffi_answers

import Base
import ../../bend/catalog_union.bend as CU
import ../../bend/ffi_catalog_union.bend as FCu
import ../../bend/wire.bend as Wr
import ../../laws/catalog_union.bend as CatalogUnion
import ./catalog_union_ffi_request_round_trip.bend as PCatalogUnionFfiRequestRoundTrip

def CatalogUnion.catalog_union_ffi_answers(bs, cs, h):
  %Equal.sym(Wr.Dec<FCu.Req>, FCu.get_req(FCu.put_req(FCu.Req{bs, cs}, "")), Wr.Got{FCu.Req{bs, cs}, ""}, CatalogUnion.catalog_union_ffi_request_round_trip(bs, cs, "", h)) : {FCu.answer(_) == FCu.put_ns(FCu.ents(CU.fast(bs, cs)), "") : String}
  {==}
