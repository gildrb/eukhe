# eukhe: the proof of LAW core_infer_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is the spelling of a request
# that fits, then its rest (IX.ix.req); an answer that is no error form
# comes from a request read whole with nothing left, and is the entry's
# reply, the spelled reply of the model's plan (IS.is.answer).

import Base
import ../../bend/ffi_infer.bend as FIn
import ../../bend/wire.bend as Wr
import ../../laws/infer.bend as Infer
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./core_infer_answers_spelled/spell.bend as IS
import ./core_infer_reads_only_requests/exact.bend as IX

def iro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FIn.Req, q => {(s, (Infer.core_infer_fits(q), a)) == (Infer.core_infer_spell_req(q, ""), (True{}, Infer.core_infer_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def iro.top_eq(+s: String, +q: FIn.Req, +a: String, e: {s == Infer.core_infer_spell_req(q, "") : String}, f: {Infer.core_infer_fits(q) == True{} : Bool}, ea: {a == Infer.core_infer_spell_answer(q) : String}) -> {(s, (Infer.core_infer_fits(q), a)) == (Infer.core_infer_spell_req(q, ""), (True{}, Infer.core_infer_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, Infer.core_infer_spell_req(q, ""), e) : {(_, (Infer.core_infer_fits(q), a)) == (Infer.core_infer_spell_req(q, ""), (True{}, Infer.core_infer_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, Infer.core_infer_fits(q), True{}, f) : {(Infer.core_infer_spell_req(q, ""), (_, a)) == (Infer.core_infer_spell_req(q, ""), (True{}, Infer.core_infer_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, Infer.core_infer_spell_answer(q), ea) : {(Infer.core_infer_spell_req(q, ""), (True{}, _)) == (Infer.core_infer_spell_req(q, ""), (True{}, Infer.core_infer_spell_answer(q))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def iro.fin(+s: String, +q: FIn.Req, r: String, pre: {s == Infer.core_infer_spell_req(q, r) : String}, f: {Infer.core_infer_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FIn.ffi.done(Wr.end(r), q)) == False{} : Bool}) -> iro.G(s, FIn.ffi.done(Wr.end(r), q)):
  match r:
    case SNil{}:
      (q, iro.top_eq(s, q, FIn.ffi.done(True{}, q), pre, f, IS.is.answer(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(iro.G(s, FIn.ffi.done(False{}, q)), ok)

def iro.main(+s: String, d: Wr.Dec<FIn.Req>, inv: IX.ix.Req(s, d), ok: {LawsBase.wire_opens_err(FIn.ffi.go(d)) == False{} : Bool}) -> iro.G(s, FIn.ffi.go(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      iro.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(iro.G(s, Wr.err("strict plan request: malformed")), ok)

def Infer.core_infer_reads_only_requests(s, ok):
  iro.main(s, FIn.get_req(s), IX.ix.req(s), ok)
