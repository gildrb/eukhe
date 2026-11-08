# eukhe: the proof of LAW catalog_union_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (cro.req of catalog_union_ffi_reads_only_requests); when
# it reads none the entry answers the malformed error, which the premise
# excludes.

import Base
import ../../bend/ffi_catalog_union.bend as FCu
import ../../bend/wire.bend as Wr
import ../../laws/catalog_union.bend as CatalogUnion
import ../wire/base/spell.bend as LAWireSpell
import ./catalog_union_ffi_reads_only_requests.bend as PCatalogUnionFfiReadsOnlyRequests

def cmu.goal(+s: String) -> Type:
  &q: FCu.Req -> &rest: String -> {(s, CatalogUnion.cu_req_fits(q)) == (CatalogUnion.cu_spell_req(q, rest), True{}) : String & Bool}

def cmu.eq(+s: String, +q: FCu.Req, +rest: String, e1: {s == CatalogUnion.cu_spell_req(q, rest) : String}, e2: {CatalogUnion.cu_req_fits(q) == True{} : Bool}) -> {(s, CatalogUnion.cu_req_fits(q)) == (CatalogUnion.cu_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, CatalogUnion.cu_spell_req(q, rest), e1) : {(_, CatalogUnion.cu_req_fits(q)) == (CatalogUnion.cu_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, CatalogUnion.cu_req_fits(q), True{}, e2) : {(CatalogUnion.cu_spell_req(q, rest), _) == (CatalogUnion.cu_spell_req(q, rest), True{}) : String & Bool}
  {==}

def cmu.main(+s: String, d: Wr.Dec<FCu.Req>, inv: PCatalogUnionFfiReadsOnlyRequests.cro.Req(s, d), other: {String.eq(FCu.answer(d), Wr.err("catalog_union: malformed request")) == False{} : Bool}) -> cmu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, cmu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmu.goal(s), other)

def CatalogUnion.catalog_union_ffi_malformed_unless_request(s, other):
  cmu.main(s, FCu.get_req(s), PCatalogUnionFfiReadsOnlyRequests.cro.req(s), other)
