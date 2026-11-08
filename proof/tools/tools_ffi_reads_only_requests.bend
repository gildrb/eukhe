# eukhe: the proof of LAW tools_ffi_reads_only_requests
#
# PROOF: the list the decoder reads is spelled and fits (NL.nl.nl); every
# code reads as a segment whose spec code is the code again (tro.back), so
# the path read is spelled and fits (tro.req); the answer is the error
# form unless the path was read whole, nothing left, and then it is the
# spelled names (tro.fin with tas.names_resolve).

import Base
import ../../bend/ffi_tools.bend as FTl
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tools.bend as Tools
import ../wire/base/spell.bend as LAWireSpell
import ./tools_ffi_reads_only_requests/nats.bend as NL
import ./tools_ffi_answers_spelled.bend as PToolsFfiAnswersSpelled

# The decoder
# -----------

# every code reads as a segment the spec codes as the code
def tro.code_back(c: Nat) -> {Tools.tools_seg_code(FTl.seg(c)) == c : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+n:
          {==}

def tro.back(cs: List<&2, Nat>) -> {Tools.tools_seg_codes(FTl.segs(cs)) == cs : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      %Equal.sym(Nat, Tools.tools_seg_code(FTl.seg(c)), c, tro.code_back(c)) : {_ <> Tools.tools_seg_codes(FTl.segs(rest)) == c <> rest : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Tools.tools_seg_codes(FTl.segs(rest)), rest, tro.back(rest)) : {c <> _ == c <> rest : List<&2, Nat>}
      {==}

# what the decoder reads is its spelling, then its rest, and fits
def tro.Req(s: String, d: Wr.Dec<List<&2, Tl.Seg>>) -> Type:
  match d:
    case Wr.Got{gs, r}:
      {s == Tools.tools_spell_req(gs, r) : String} & {Tools.tools_req_fits(gs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tro.fits(+cs: List<&2, Nat>, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)) == True{} : Bool}) -> {Tools.tools_req_fits(FTl.segs(cs)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, Tools.tools_seg_codes(FTl.segs(cs)), cs, tro.back(cs)) : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(Tools.tools_seg_codes(FTl.segs(cs)))) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, Tools.tools_seg_codes(FTl.segs(cs)), cs, tro.back(cs)) : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(_)) == True{} : Bool}
  f

def tro.of(+s: String, d: Wr.Dec<List<&2, Nat>>, xd: NL.nl.NL(s, d)) -> tro.Req(s, FTl.get_req.of(d)):
  match d:
    case Wr.Got{+cs, +r}:
      (e, f) = xd
      (Equal.trans(String, s, LawsBase.wire_spell_nats(cs, r), LawsBase.wire_spell_nats(Tools.tools_seg_codes(FTl.segs(cs)), r), e, Equal.cong(List<&2, Nat>, String, z => LawsBase.wire_spell_nats(z, r), cs, Tools.tools_seg_codes(FTl.segs(cs)), Equal.sym(List<&2, Nat>, Tools.tools_seg_codes(FTl.segs(cs)), cs, tro.back(cs)))), tro.fits(cs, f))
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled path that fits, then
# the rest
def tro.req(+s: String) -> tro.Req(s, FTl.get_req(s)):
  tro.of(s, Wr.get_list(~Nat, ~Wr.get_nat, s), NL.nl.nl(s))

# The entry
# ---------

def tro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, List<&2, Tl.Seg>, gs => {(s, (Tools.tools_req_fits(gs), a)) == (Tools.tools_spell_req(gs, ""), (True{}, Tools.tools_spell_answer(gs))) : String & (Bool & String)}>

# a path read whole: the input, the fit and the answer are the spec's
def tro.top_eq(+s: String, +gs: List<&2, Tl.Seg>, +a: String, e: {s == Tools.tools_spell_req(gs, "") : String}, f: {Tools.tools_req_fits(gs) == True{} : Bool}, ea: {a == Tools.tools_spell_answer(gs) : String}) -> {(s, (Tools.tools_req_fits(gs), a)) == (Tools.tools_spell_req(gs, ""), (True{}, Tools.tools_spell_answer(gs))) : String & (Bool & String)}:
  %Equal.sym(String, s, Tools.tools_spell_req(gs, ""), e) : {(_, (Tools.tools_req_fits(gs), a)) == (Tools.tools_spell_req(gs, ""), (True{}, Tools.tools_spell_answer(gs))) : String & (Bool & String)}
  %Equal.sym(Bool, Tools.tools_req_fits(gs), True{}, f) : {(Tools.tools_spell_req(gs, ""), (_, a)) == (Tools.tools_spell_req(gs, ""), (True{}, Tools.tools_spell_answer(gs))) : String & (Bool & String)}
  %Equal.sym(String, a, Tools.tools_spell_answer(gs), ea) : {(Tools.tools_spell_req(gs, ""), (True{}, _)) == (Tools.tools_spell_req(gs, ""), (True{}, Tools.tools_spell_answer(gs))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the path, anything left is the
# error form
def tro.fin(+s: String, +gs: List<&2, Tl.Seg>, r: String, pre: {s == Tools.tools_spell_req(gs, r) : String}, f: {Tools.tools_req_fits(gs) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FTl.reply(Wr.end(r), gs)) == False{} : Bool}) -> tro.G(s, FTl.reply(Wr.end(r), gs)):
  match r:
    case SNil{}:
      (gs, tro.top_eq(s, gs, FTl.reply(True{}, gs), pre, f, PToolsFfiAnswersSpelled.tas.names_resolve(gs)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(tro.G(s, FTl.reply(False{}, gs)), ok)

def tro.main(+s: String, d: Wr.Dec<List<&2, Tl.Seg>>, inv: tro.Req(s, d), ok: {LawsBase.wire_opens_err(FTl.answer(d)) == False{} : Bool}) -> tro.G(s, FTl.answer(d)):
  match d:
    case Wr.Got{+gs, +r}:
      (e, f) = inv
      tro.fin(s, gs, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(tro.G(s, Wr.err("tools: malformed request")), ok)

def Tools.tools_ffi_reads_only_requests(s, ok):
  tro.main(s, FTl.get_req(s), tro.req(s), ok)
