# eukhe: the proof of LAW tool_surface_ffi_reads_only_requests
#
# PROOF: what the entry's decoder reads is the spelling of a request whose
# numbers fit, then its rest (tso.req: the tag by wire_nat_exact, the list
# by the shared list lemma NL.nl.nl, the Nat after it by wire_nat_exact
# and wire_nat_decoded_fits; a tag of 4 or more reads nothing); the answer
# is the error form unless the request was read whole, nothing left, and
# then it is the model's decision, spelled (LATs.ts.reply).

import Base
import ../../bend/ffi_tool_surface.bend as FTs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tool_surface.bend as ToolSurface
import ../../laws/wire.bend as Wire
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../tools/tools_ffi_reads_only_requests/nats.bend as NL
import ./base.bend as LATs

# The decoder
# -----------

# what the decoder reads is its spelling, then its rest, and fits
def tso.Req(s: String, d: Wr.Dec<FTs.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ToolSurface.spell_req(q, r) : String} & {ToolSurface.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a list spelled by the list lemma is the laws' spelling of it
def tso.ns(-s1: String, +xs: List<&2, Nat>, +s2: String, e: {s1 == LawsBase.wire_spell_nats(xs, s2) : String}) -> {s1 == ToolSurface.spell_ns(xs, s2) : String}:
  Equal.trans(String, s1, LawsBase.wire_spell_nats(xs, s2), ToolSurface.spell_ns(xs, s2), e, Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, s2), LawsBase.wire_spell_nats(xs, s2), Wire.wire_nats_spells(xs, s2)))

# tag 0n: the Nat after the list
def tso.b_n(+s: String, +ps: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(0n, ToolSurface.spell_ns(ps, s2)) : String}, fl: {ToolSurface.ns_fit(ps) == True{} : Bool}, r: Wr.Dec<Nat>, +er: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}) -> tso.Req(s, FTs.get_build.version(ps, r)):
  match r:
    case Wr.Got{+v, +s3}:
      (NL.nl.step(z => Wr.put_nat(0n, ToolSurface.spell_ns(ps, z)), s, s2, Wr.put_nat(v, s3), pre, Wire.wire_nat_exact(s2, v, s3, er)), LAWireSpell.ws_and_tt(ToolSurface.ns_fit(ps), LawsBase.wire_fits(v), fl, Wire.wire_nat_decoded_fits(s2, v, s3, er)))
    case Wr.Bad{}:
      Unit{}

# tag 0n: the list
def tso.b_l(+s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d1: Wr.Dec<List<&2, Nat>>, ed: NL.nl.NL(s1, d1)) -> tso.Req(s, FTs.get_build(d1)):
  match d1:
    case Wr.Got{+ps, +s2}:
      (e, f) = ed
      tso.b_n(s, ps, s2, NL.nl.step(z => Wr.put_nat(0n, z), s, s1, ToolSurface.spell_ns(ps, s2), pre, tso.ns(s1, ps, s2, e)), f, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

# tag 1n: the Nat after the list
def tso.j_n(+s: String, +d: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(1n, ToolSurface.spell_ns(d, s2)) : String}, fl: {ToolSurface.ns_fit(d) == True{} : Bool}, r: Wr.Dec<Nat>, +er: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}) -> tso.Req(s, FTs.get_join.t(d, r)):
  match r:
    case Wr.Got{+t, +s3}:
      (NL.nl.step(z => Wr.put_nat(1n, ToolSurface.spell_ns(d, z)), s, s2, Wr.put_nat(t, s3), pre, Wire.wire_nat_exact(s2, t, s3, er)), LAWireSpell.ws_and_tt(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fl, Wire.wire_nat_decoded_fits(s2, t, s3, er)))
    case Wr.Bad{}:
      Unit{}

# tag 1n: the list
def tso.j_l(+s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d1: Wr.Dec<List<&2, Nat>>, ed: NL.nl.NL(s1, d1)) -> tso.Req(s, FTs.get_join(d1)):
  match d1:
    case Wr.Got{+d, +s2}:
      (e, f) = ed
      tso.j_n(s, d, s2, NL.nl.step(z => Wr.put_nat(1n, z), s, s1, ToolSurface.spell_ns(d, s2), pre, tso.ns(s1, d, s2, e)), f, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

# tag 2n: the Nat after the list
def tso.q_n(+s: String, +d: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(2n, ToolSurface.spell_ns(d, s2)) : String}, fl: {ToolSurface.ns_fit(d) == True{} : Bool}, r: Wr.Dec<Nat>, +er: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}) -> tso.Req(s, FTs.get_quit.t(d, r)):
  match r:
    case Wr.Got{+t, +s3}:
      (NL.nl.step(z => Wr.put_nat(2n, ToolSurface.spell_ns(d, z)), s, s2, Wr.put_nat(t, s3), pre, Wire.wire_nat_exact(s2, t, s3, er)), LAWireSpell.ws_and_tt(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fl, Wire.wire_nat_decoded_fits(s2, t, s3, er)))
    case Wr.Bad{}:
      Unit{}

# tag 2n: the list
def tso.q_l(+s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d1: Wr.Dec<List<&2, Nat>>, ed: NL.nl.NL(s1, d1)) -> tso.Req(s, FTs.get_quit(d1)):
  match d1:
    case Wr.Got{+d, +s2}:
      (e, f) = ed
      tso.q_n(s, d, s2, NL.nl.step(z => Wr.put_nat(2n, z), s, s1, ToolSurface.spell_ns(d, s2), pre, tso.ns(s1, d, s2, e)), f, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

# tag 3n: the Nat after the list
def tso.r_n(+s: String, +d: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(3n, ToolSurface.spell_ns(d, s2)) : String}, fl: {ToolSurface.ns_fit(d) == True{} : Bool}, r: Wr.Dec<Nat>, +er: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}) -> tso.Req(s, FTs.get_reach.t(d, r)):
  match r:
    case Wr.Got{+t, +s3}:
      (NL.nl.step(z => Wr.put_nat(3n, ToolSurface.spell_ns(d, z)), s, s2, Wr.put_nat(t, s3), pre, Wire.wire_nat_exact(s2, t, s3, er)), LAWireSpell.ws_and_tt(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fl, Wire.wire_nat_decoded_fits(s2, t, s3, er)))
    case Wr.Bad{}:
      Unit{}

# tag 3n: the list
def tso.r_l(+s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d1: Wr.Dec<List<&2, Nat>>, ed: NL.nl.NL(s1, d1)) -> tso.Req(s, FTs.get_reach(d1)):
  match d1:
    case Wr.Got{+d, +s2}:
      (e, f) = ed
      tso.r_n(s, d, s2, NL.nl.step(z => Wr.put_nat(3n, z), s, s1, ToolSurface.spell_ns(d, s2), pre, tso.ns(s1, d, s2, e)), f, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def tso.tag(+s: String, t: Nat, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tso.Req(s, FTs.get_req.tag(t, s1)):
  match t:
    case 0n:
      tso.b_l(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), NL.nl.nl(s1))
    case 1n:
      tso.j_l(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), NL.nl.nl(s1))
    case 2n:
      tso.q_l(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), NL.nl.nl(s1))
    case 3n:
      tso.r_l(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), NL.nl.nl(s1))
    case 4n+u:
      Unit{}

def tso.go(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> tso.Req(s, FTs.get_req.go(r)):
  match r:
    case Wr.Got{+t, +s1}:
      tso.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, er))
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def tso.req(+s: String) -> tso.Req(s, FTs.get_req(s)):
  tso.go(s, Wr.get_nat(s), {==})

# The entry
# ---------

def tso.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FTs.Req, q => {(s, (ToolSurface.req_fits(q), a)) == (ToolSurface.spell_req(q, ""), (True{}, ToolSurface.spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the laws'
def tso.top_eq(+s: String, +q: FTs.Req, +a: String, e: {s == ToolSurface.spell_req(q, "") : String}, f: {ToolSurface.req_fits(q) == True{} : Bool}, ea: {a == ToolSurface.spell_answer(q) : String}) -> {(s, (ToolSurface.req_fits(q), a)) == (ToolSurface.spell_req(q, ""), (True{}, ToolSurface.spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, ToolSurface.spell_req(q, ""), e) : {(_, (ToolSurface.req_fits(q), a)) == (ToolSurface.spell_req(q, ""), (True{}, ToolSurface.spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, ToolSurface.req_fits(q), True{}, f) : {(ToolSurface.spell_req(q, ""), (_, a)) == (ToolSurface.spell_req(q, ""), (True{}, ToolSurface.spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, ToolSurface.spell_answer(q), ea) : {(ToolSurface.spell_req(q, ""), (True{}, _)) == (ToolSurface.spell_req(q, ""), (True{}, ToolSurface.spell_answer(q))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def tso.fin(+s: String, +q: FTs.Req, r: String, pre: {s == ToolSurface.spell_req(q, r) : String}, f: {ToolSurface.req_fits(q) == True{} : Bool}, ok: {String.eq(FTs.run.end(Wr.end(r), q), ToolSurface.malformed()) == False{} : Bool}) -> tso.G(s, FTs.run.end(Wr.end(r), q)):
  match r:
    case SNil{}:
      (q, tso.top_eq(s, q, FTs.answer(q), pre, f, LATs.ts.reply(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(tso.G(s, FTs.run.end(False{}, q)), ok)

def tso.main(+s: String, d: Wr.Dec<FTs.Req>, inv: tso.Req(s, d), ok: {String.eq(FTs.run(d), ToolSurface.malformed()) == False{} : Bool}) -> tso.G(s, FTs.run(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      tso.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(tso.G(s, FTs.malformed()), ok)

def ToolSurface.tool_surface_ffi_reads_only_requests(s, other):
  tso.main(s, FTs.get_req(s), tso.req(s), other)
