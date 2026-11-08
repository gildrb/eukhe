# eukhe: the proof of LAW dir_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (pdx.req); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director
import ../wire/base/spell.bend as LAWireSpell
import ./dir_ffi_reads_only_requests/exact.bend as LX

def pdmu.goal(+s: String) -> Type:
  &q: FDr.Req -> &rest: String -> {(s, Director.dir_req_fits(q)) == (Director.dir_spell_req(q, rest), True{}) : String & Bool}

def pdmu.eq(+s: String, +q: FDr.Req, +rest: String, e1: {s == Director.dir_spell_req(q, rest) : String}, e2: {Director.dir_req_fits(q) == True{} : Bool}) -> {(s, Director.dir_req_fits(q)) == (Director.dir_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Director.dir_spell_req(q, rest), e1) : {(_, Director.dir_req_fits(q)) == (Director.dir_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Director.dir_req_fits(q), True{}, e2) : {(Director.dir_spell_req(q, rest), _) == (Director.dir_spell_req(q, rest), True{}) : String & Bool}
  {==}

def pdmu.main(+s: String, d: Wr.Dec<FDr.Req>, inv: LX.pdx.RP(s, d), other: {String.eq(FDr.ffi.go(d), Wr.err("director: malformed request")) == False{} : Bool}) -> pdmu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, pdmu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(pdmu.goal(s), other)

def Director.dir_ffi_malformed_unless_request(s, other):
  pdmu.main(s, FDr.get_req(s), LX.pdx.req(s), other)
