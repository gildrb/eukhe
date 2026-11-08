# eukhe: the proof of LAW catalog_union_ffi_left_over_spelled
#
# PROOF: the spec's spelling is the entry's put_req (cua.req), which reads
# back with the rest untouched (catalog_union_ffi_request_round_trip); a
# rest that is not empty answers the left-over error.

import Base
import ../../bend/ffi_catalog_union.bend as FCu
import ../../bend/wire.bend as Wr
import ../../laws/catalog_union.bend as CatalogUnion
import ./catalog_union_ffi_request_round_trip.bend as PCatalogUnionFfiRequestRoundTrip
import ./catalog_union_ffi_answers_spelled.bend as PCatalogUnionFfiAnswersSpelled

def cul.main(q: FCu.Req, fits: {CatalogUnion.cu_req_fits(q) == True{} : Bool}, +ch: Char, +t: String) -> {FCu.ffi(CatalogUnion.cu_spell_req(q, SCon{ch, t})) == Wr.err("catalog_union: input left over") : String}:
  match q:
    case FCu.Req{+b, +c}:
      %PCatalogUnionFfiAnswersSpelled.cua.req(b, c, SCon{ch, t}) : {FCu.ffi(_) == Wr.err("catalog_union: input left over") : String}
      %Equal.sym(Wr.Dec<FCu.Req>, FCu.get_req(FCu.put_req(FCu.Req{b, c}, SCon{ch, t})), Wr.Got{FCu.Req{b, c}, SCon{ch, t}}, CatalogUnion.catalog_union_ffi_request_round_trip(b, c, SCon{ch, t}, PCatalogUnionFfiAnswersSpelled.cua.fits(b, c, fits))) : {FCu.answer(_) == Wr.err("catalog_union: input left over") : String}
      {==}

def CatalogUnion.catalog_union_ffi_left_over_spelled(q, fits, c, t):
  cul.main(q, fits, c, t)
