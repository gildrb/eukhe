# eukhe: the proof of LAW afw_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is the spelling of what it
# read, then its rest, and fits the wire (EX.afx.req, field by field with
# the wire's exactness laws: an unknown tag is Bad); so an answer that is
# no error comes from a request read whole, nothing left, and is the
# spelled spec decision (LA.pfs.answer).

import Base
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA
import ./afw_reads_only_requests/exact.bend as EX

def afro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FAf.Req, x => {(s, (AuxFallback.afw_req_fits(x), a)) == (AuxFallback.afw_spell_req(x, ""), (True{}, AuxFallback.afw_spell_answer(x))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def afro.top_eq(+s: String, +x: FAf.Req, +a: String, e: {s == AuxFallback.afw_spell_req(x, "") : String}, f: {AuxFallback.afw_req_fits(x) == True{} : Bool}, ea: {a == AuxFallback.afw_spell_answer(x) : String}) -> {(s, (AuxFallback.afw_req_fits(x), a)) == (AuxFallback.afw_spell_req(x, ""), (True{}, AuxFallback.afw_spell_answer(x))) : String & (Bool & String)}:
  %Equal.sym(String, s, AuxFallback.afw_spell_req(x, ""), e) : {(_, (AuxFallback.afw_req_fits(x), a)) == (AuxFallback.afw_spell_req(x, ""), (True{}, AuxFallback.afw_spell_answer(x))) : String & (Bool & String)}
  %Equal.sym(Bool, AuxFallback.afw_req_fits(x), True{}, f) : {(AuxFallback.afw_spell_req(x, ""), (_, a)) == (AuxFallback.afw_spell_req(x, ""), (True{}, AuxFallback.afw_spell_answer(x))) : String & (Bool & String)}
  %Equal.sym(String, a, AuxFallback.afw_spell_answer(x), ea) : {(AuxFallback.afw_spell_req(x, ""), (True{}, _)) == (AuxFallback.afw_spell_req(x, ""), (True{}, AuxFallback.afw_spell_answer(x))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def afro.fin(+s: String, +x: FAf.Req, r: String, pre: {s == AuxFallback.afw_spell_req(x, r) : String}, f: {AuxFallback.afw_req_fits(x) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FAf.ffi.end(Wr.end(r), x)) == False{} : Bool}) -> afro.G(s, FAf.ffi.end(Wr.end(r), x)):
  match r:
    case SNil{}:
      (x, afro.top_eq(s, x, FAf.ffi.end(True{}, x), pre, f, LA.pfs.answer(x)))
    case SCon{c, y}:
      LAWireSpell.ws_absurd(afro.G(s, FAf.ffi.end(False{}, x)), ok)

def afro.main(+s: String, d: Wr.Dec<FAf.Req>, inv: EX.afx.PQ(s, d), ok: {LawsBase.wire_opens_err(FAf.ffi.go(d)) == False{} : Bool}) -> afro.G(s, FAf.ffi.go(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = inv
      afro.fin(s, x, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(afro.G(s, Wr.err("aux_fallback: malformed request")), ok)

def AuxFallback.afw_reads_only_requests(s, ok):
  afro.main(s, FAf.get_req(s), EX.afx.req(s), ok)
