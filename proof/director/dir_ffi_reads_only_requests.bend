# eukhe: the proof of LAW dir_ffi_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is the spelled request, then
# its rest, and fits the wire (pdx.req); an answer that is no error comes
# from a request read whole, nothing left, and is the spelled loop after
# the tick (pds.answer).

import Base
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./dir_ffi_answers_spelled/spell.bend as LS
import ./dir_ffi_reads_only_requests/exact.bend as LX

def pdro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FDr.Req, q => {(s, (Director.dir_req_fits(q), a)) == (Director.dir_spell_req(q, ""), (True{}, Director.dir_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def pdro.top_eq(+s: String, +q: FDr.Req, +a: String, e: {s == Director.dir_spell_req(q, "") : String}, f: {Director.dir_req_fits(q) == True{} : Bool}, ea: {a == Director.dir_spell_answer(q) : String}) -> {(s, (Director.dir_req_fits(q), a)) == (Director.dir_spell_req(q, ""), (True{}, Director.dir_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, Director.dir_spell_req(q, ""), e) : {(_, (Director.dir_req_fits(q), a)) == (Director.dir_spell_req(q, ""), (True{}, Director.dir_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, Director.dir_req_fits(q), True{}, f) : {(Director.dir_spell_req(q, ""), (_, a)) == (Director.dir_spell_req(q, ""), (True{}, Director.dir_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, Director.dir_spell_answer(q), ea) : {(Director.dir_spell_req(q, ""), (True{}, _)) == (Director.dir_spell_req(q, ""), (True{}, Director.dir_spell_answer(q))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def pdro.fin(+s: String, +q: FDr.Req, r: String, pre: {s == Director.dir_spell_req(q, r) : String}, f: {Director.dir_req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FDr.ffi.whole(q, Wr.end(r))) == False{} : Bool}) -> pdro.G(s, FDr.ffi.whole(q, Wr.end(r))):
  match r:
    case SNil{}:
      (q, pdro.top_eq(s, q, FDr.ffi.run(q), pre, f, LS.pds.answer(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(pdro.G(s, FDr.ffi.whole(q, False{})), ok)

def pdro.main(+s: String, d: Wr.Dec<FDr.Req>, inv: LX.pdx.RP(s, d), ok: {LawsBase.wire_opens_err(FDr.ffi.go(d)) == False{} : Bool}) -> pdro.G(s, FDr.ffi.go(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      pdro.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(pdro.G(s, Wr.err("director: malformed request")), ok)

def Director.dir_ffi_reads_only_requests(s, ok):
  pdro.main(s, FDr.get_req(s), LX.pdx.req(s), ok)
