# eukhe: the proof of LAW afw_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (EX.afx.req); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback/wire.bend as AuxFallbackWire
import ../wire/base/spell.bend as LAWireSpell
import ./afw_reads_only_requests/exact.bend as EX

def afmu.goal(+s: String) -> Type:
  &x: FAf.Req -> &rest: String -> {(s, AuxFallbackWire.afw_req_fits(x)) == (AuxFallbackWire.afw_spell_req(x, rest), True{}) : String & Bool}

def afmu.eq(+s: String, +x: FAf.Req, +rest: String, e1: {s == AuxFallbackWire.afw_spell_req(x, rest) : String}, e2: {AuxFallbackWire.afw_req_fits(x) == True{} : Bool}) -> {(s, AuxFallbackWire.afw_req_fits(x)) == (AuxFallbackWire.afw_spell_req(x, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, AuxFallbackWire.afw_spell_req(x, rest), e1) : {(_, AuxFallbackWire.afw_req_fits(x)) == (AuxFallbackWire.afw_spell_req(x, rest), True{}) : String & Bool}
  %Equal.sym(Bool, AuxFallbackWire.afw_req_fits(x), True{}, e2) : {(AuxFallbackWire.afw_spell_req(x, rest), _) == (AuxFallbackWire.afw_spell_req(x, rest), True{}) : String & Bool}
  {==}

def afmu.main(+s: String, d: Wr.Dec<FAf.Req>, inv: EX.afx.PQ(s, d), other: {String.eq(FAf.ffi.go(d), Wr.err("aux_fallback: malformed request")) == False{} : Bool}) -> afmu.goal(s):
  match d:
    case Wr.Got{+x, +rest}:
      (e1, e2) = inv
      (x, (rest, afmu.eq(s, x, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(afmu.goal(s), other)

def AuxFallbackWire.afw_malformed_unless_request(s, other):
  afmu.main(s, FAf.get_req(s), EX.afx.req(s), other)
