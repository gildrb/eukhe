# eukhe: the proof of LAW orphan_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (oc.req of orphan_ffi_reads_only_requests); when it reads
# none the entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/orphan.bend as Orphan
import ../wire/base/spell.bend as LAWireSpell
import ./orphan_ffi_reads_only_requests.bend as POrphanFfiReadsOnlyRequests

def omu.goal(+s: String) -> Type:
  &q: FO.Req -> &rest: String -> {(s, Orphan.orphan_req_fits(q)) == (Orphan.orphan_spell_req(q, rest), True{}) : String & Bool}

def omu.eq(+s: String, +q: FO.Req, +rest: String, e1: {s == Orphan.orphan_spell_req(q, rest) : String}, e2: {Orphan.orphan_req_fits(q) == True{} : Bool}) -> {(s, Orphan.orphan_req_fits(q)) == (Orphan.orphan_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Orphan.orphan_spell_req(q, rest), e1) : {(_, Orphan.orphan_req_fits(q)) == (Orphan.orphan_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Orphan.orphan_req_fits(q), True{}, e2) : {(Orphan.orphan_spell_req(q, rest), _) == (Orphan.orphan_spell_req(q, rest), True{}) : String & Bool}
  {==}

def omu.main(+s: String, d: Wr.Dec<FO.Req>, inv: POrphanFfiReadsOnlyRequests.oc.Req(s, d), other: {String.eq(FO.ffi.go(d), Wr.err("orphan: malformed request")) == False{} : Bool}) -> omu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, omu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(omu.goal(s), other)

def Orphan.orphan_ffi_malformed_unless_request(s, other):
  omu.main(s, FO.get_req(s), POrphanFfiReadsOnlyRequests.oc.req(s), other)
