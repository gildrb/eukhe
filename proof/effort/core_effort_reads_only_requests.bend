# eukhe: the proof of LAW core_effort_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is the spelling of a request
# that fits, then its rest (EX.ex.req); an answer that is no error form
# comes from a request read whole with nothing left, and is the entry's
# reply, the spelled reply of the model's decision (ES.es.answer).

import Base
import ../../bend/ffi_effort.bend as FEf
import ../../bend/wire.bend as Wr
import ../../laws/effort.bend as Effort
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./core_effort_answers_spelled/spell.bend as ES
import ./core_effort_reads_only_requests/exact.bend as EX

def ro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FEf.Req, q => {(s, (Effort.core_effort_fits(q), a)) == (Effort.core_effort_spell_req(q, ""), (True{}, Effort.core_effort_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def ro.top_eq(+s: String, +q: FEf.Req, +a: String, e: {s == Effort.core_effort_spell_req(q, "") : String}, f: {Effort.core_effort_fits(q) == True{} : Bool}, ea: {a == Effort.core_effort_spell_answer(q) : String}) -> {(s, (Effort.core_effort_fits(q), a)) == (Effort.core_effort_spell_req(q, ""), (True{}, Effort.core_effort_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, Effort.core_effort_spell_req(q, ""), e) : {(_, (Effort.core_effort_fits(q), a)) == (Effort.core_effort_spell_req(q, ""), (True{}, Effort.core_effort_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, Effort.core_effort_fits(q), True{}, f) : {(Effort.core_effort_spell_req(q, ""), (_, a)) == (Effort.core_effort_spell_req(q, ""), (True{}, Effort.core_effort_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, Effort.core_effort_spell_answer(q), ea) : {(Effort.core_effort_spell_req(q, ""), (True{}, _)) == (Effort.core_effort_spell_req(q, ""), (True{}, Effort.core_effort_spell_answer(q))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def ro.fin(+s: String, +q: FEf.Req, r: String, pre: {s == Effort.core_effort_spell_req(q, r) : String}, f: {Effort.core_effort_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FEf.ffi.done(Wr.end(r), q)) == False{} : Bool}) -> ro.G(s, FEf.ffi.done(Wr.end(r), q)):
  match r:
    case SNil{}:
      (q, ro.top_eq(s, q, FEf.ffi.done(True{}, q), pre, f, ES.es.answer(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(ro.G(s, FEf.ffi.done(False{}, q)), ok)

def ro.main(+s: String, d: Wr.Dec<FEf.Req>, inv: EX.ex.Req(s, d), ok: {LawsBase.wire_opens_err(FEf.ffi.go(d)) == False{} : Bool}) -> ro.G(s, FEf.ffi.go(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      ro.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("ladder request: malformed")), ok)

def Effort.core_effort_reads_only_requests(s, ok):
  ro.main(s, FEf.get_req(s), EX.ex.req(s), ok)
