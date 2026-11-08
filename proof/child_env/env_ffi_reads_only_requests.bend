# eukhe: the proof of LAW env_ffi_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is the spelled request, then
# its rest, and fits the wire (pex.req); an answer that is no error comes
# from a request read whole, nothing left, and is the spelled environment
# of the child (pes.answer).

import Base
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./env_ffi_answers_spelled/spell.bend as LS
import ./env_ffi_reads_only_requests/exact.bend as LX

def pero.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FEnv.Req, q => {(s, (ChildEnv.env_req_fits(q), a)) == (ChildEnv.env_spell_req(q, ""), (True{}, ChildEnv.env_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def pero.top_eq(+s: String, +q: FEnv.Req, +a: String, e: {s == ChildEnv.env_spell_req(q, "") : String}, f: {ChildEnv.env_req_fits(q) == True{} : Bool}, ea: {a == ChildEnv.env_spell_answer(q) : String}) -> {(s, (ChildEnv.env_req_fits(q), a)) == (ChildEnv.env_spell_req(q, ""), (True{}, ChildEnv.env_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, ChildEnv.env_spell_req(q, ""), e) : {(_, (ChildEnv.env_req_fits(q), a)) == (ChildEnv.env_spell_req(q, ""), (True{}, ChildEnv.env_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, ChildEnv.env_req_fits(q), True{}, f) : {(ChildEnv.env_spell_req(q, ""), (_, a)) == (ChildEnv.env_spell_req(q, ""), (True{}, ChildEnv.env_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, ChildEnv.env_spell_answer(q), ea) : {(ChildEnv.env_spell_req(q, ""), (True{}, _)) == (ChildEnv.env_spell_req(q, ""), (True{}, ChildEnv.env_spell_answer(q))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def pero.fin(+s: String, +q: FEnv.Req, r: String, pre: {s == ChildEnv.env_spell_req(q, r) : String}, f: {ChildEnv.env_req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FEnv.ffi.whole(q, Wr.end(r))) == False{} : Bool}) -> pero.G(s, FEnv.ffi.whole(q, Wr.end(r))):
  match r:
    case SNil{}:
      (q, pero.top_eq(s, q, FEnv.ffi.run(q), pre, f, LS.pes.answer(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(pero.G(s, FEnv.ffi.whole(q, False{})), ok)

def pero.main(+s: String, d: Wr.Dec<FEnv.Req>, inv: LX.pex.RP(s, d), ok: {LawsBase.wire_opens_err(FEnv.ffi.go(d)) == False{} : Bool}) -> pero.G(s, FEnv.ffi.go(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      pero.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(pero.G(s, Wr.err("child_env: malformed request")), ok)

def ChildEnv.env_ffi_reads_only_requests(s, ok):
  pero.main(s, FEnv.get_req(s), LX.pex.req(s), ok)
