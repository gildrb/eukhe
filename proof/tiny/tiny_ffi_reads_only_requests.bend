# eukhe: the proof of LAW tiny_ffi_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is the spelling of a request
# that fits, then its rest (tro.req: each list read is spelled and fits,
# NL.nl.nl); the answer is the error form unless the request was read
# whole, nothing left, and then it is the spelled pick (tro.fin with
# tas.pick).

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/tiny.bend as Tn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/pick.bend as Tiny
import ../wire/base/spell.bend as LAWireSpell
import ../tools/tools_ffi_reads_only_requests/nats.bend as NL
import ./tiny_ffi_answers_spelled.bend as PTinyFfiAnswersSpelled

# The decoder
# -----------

# what the decoder reads is its spelling, then its rest, and fits
def tro.Req(s: String, d: Wr.Dec<FTn.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Tiny.tiny_spell_req(q, r) : String} & {Tiny.tiny_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tro.up(+s: String, +c: List<&2, Nat>, +s1: String, pre: {s == LawsBase.wire_spell_nats(c, s1) : String}, fc: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, c)), LawsBase.wire_nats_fit(c)) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, xd: NL.nl.NL(s1, d)) -> tro.Req(s, FTn.get_req.up(c, d)):
  match d:
    case Wr.Got{+u, +s2}:
      (e, fu) = xd
      (NL.nl.step(z => LawsBase.wire_spell_nats(c, z), s, s1, LawsBase.wire_spell_nats(u, s2), pre, e), LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, c)), LawsBase.wire_nats_fit(c)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, u)), LawsBase.wire_nats_fit(u)), fc, fu))
    case Wr.Bad{}:
      Unit{}

def tro.chain(+s: String, d: Wr.Dec<List<&2, Nat>>, xd: NL.nl.NL(s, d)) -> tro.Req(s, FTn.get_req.chain(d)):
  match d:
    case Wr.Got{+c, +s1}:
      (e, fc) = xd
      tro.up(s, c, s1, e, fc, FTn.get_ids(s1), NL.nl.nl(s1))
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def tro.req(+s: String) -> tro.Req(s, FTn.get_req(s)):
  tro.chain(s, FTn.get_ids(s), NL.nl.nl(s))

# The entry
# ---------

def tro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FTn.Req, q => {(s, (Tiny.tiny_req_fits(q), a)) == (Tiny.tiny_spell_req(q, ""), (True{}, Tiny.tiny_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def tro.top_eq(+s: String, +q: FTn.Req, +a: String, e: {s == Tiny.tiny_spell_req(q, "") : String}, f: {Tiny.tiny_req_fits(q) == True{} : Bool}, ea: {a == Tiny.tiny_spell_answer(q) : String}) -> {(s, (Tiny.tiny_req_fits(q), a)) == (Tiny.tiny_spell_req(q, ""), (True{}, Tiny.tiny_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, Tiny.tiny_spell_req(q, ""), e) : {(_, (Tiny.tiny_req_fits(q), a)) == (Tiny.tiny_spell_req(q, ""), (True{}, Tiny.tiny_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, Tiny.tiny_req_fits(q), True{}, f) : {(Tiny.tiny_spell_req(q, ""), (_, a)) == (Tiny.tiny_spell_req(q, ""), (True{}, Tiny.tiny_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, Tiny.tiny_spell_answer(q), ea) : {(Tiny.tiny_spell_req(q, ""), (True{}, _)) == (Tiny.tiny_spell_req(q, ""), (True{}, Tiny.tiny_spell_answer(q))) : String & (Bool & String)}
  {==}

# the entry's reply to a request read whole is the spelled pick
def tro.ans(q: FTn.Req) -> {FTn.reply(True{}, q) == Tiny.tiny_spell_answer(q) : String}:
  match q:
    case FTn.Req{+c, +u}:
      PTinyFfiAnswersSpelled.tas.pick(Tn.pick(c, u))

# the end check: nothing left answers the request, anything left is the
# error form
def tro.fin(+s: String, +q: FTn.Req, r: String, pre: {s == Tiny.tiny_spell_req(q, r) : String}, f: {Tiny.tiny_req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FTn.reply(Wr.end(r), q)) == False{} : Bool}) -> tro.G(s, FTn.reply(Wr.end(r), q)):
  match r:
    case SNil{}:
      (q, tro.top_eq(s, q, FTn.reply(True{}, q), pre, f, tro.ans(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(tro.G(s, FTn.reply(False{}, q)), ok)

def tro.main(+s: String, d: Wr.Dec<FTn.Req>, inv: tro.Req(s, d), ok: {LawsBase.wire_opens_err(FTn.answer(d)) == False{} : Bool}) -> tro.G(s, FTn.answer(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      tro.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(tro.G(s, Wr.err("tiny: malformed request")), ok)

def Tiny.tiny_ffi_reads_only_requests(s, ok):
  tro.main(s, FTn.get_req(s), tro.req(s), ok)
