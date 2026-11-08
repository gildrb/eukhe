# eukhe: the proof of LAW wire_ffi_reads_only_requests
#
# PROOF: each field the entry reads is exactly its spelling, then its rest
# (the wire's exactness laws), and the numbers and lengths read fit
# (decoded_fits; a decoded list: LA.wrb.nats_fit); the stages carry the
# input spelled up to their field (`pre`), so an answer that is no error
# comes from a request read whole, nothing left, and is its spelling
# written again (LA.wrb.spell).

import Base
import ../../bend/ffi_wire.bend as FWi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/wire_ffi.bend as WireFfi
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_u32_exact.bend as PWireU32Exact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA

def ro.G(s: String, ans: String) -> Type:
  Sigma<&1, &1, WireFfi.wr.Req, q => {(s, (WireFfi.wr_fits(q), ans)) == (WireFfi.wr_spell(q, ""), (True{}, WireFfi.wr_spell(q, ""))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def ro.top(+s: String, +q: WireFfi.wr.Req, +ans: String, e: {s == WireFfi.wr_spell(q, "") : String}, f: {WireFfi.wr_fits(q) == True{} : Bool}, ea: {ans == WireFfi.wr_spell(q, "") : String}) -> {(s, (WireFfi.wr_fits(q), ans)) == (WireFfi.wr_spell(q, ""), (True{}, WireFfi.wr_spell(q, ""))) : String & (Bool & String)}:
  %Equal.sym(String, s, WireFfi.wr_spell(q, ""), e) : {(_, (WireFfi.wr_fits(q), ans)) == (WireFfi.wr_spell(q, ""), (True{}, WireFfi.wr_spell(q, ""))) : String & (Bool & String)}
  %Equal.sym(Bool, WireFfi.wr_fits(q), True{}, f) : {(WireFfi.wr_spell(q, ""), (_, ans)) == (WireFfi.wr_spell(q, ""), (True{}, WireFfi.wr_spell(q, ""))) : String & (Bool & String)}
  %Equal.sym(String, ans, WireFfi.wr_spell(q, ""), ea) : {(WireFfi.wr_spell(q, ""), (True{}, _)) == (WireFfi.wr_spell(q, ""), (True{}, WireFfi.wr_spell(q, ""))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def ro.fin(r: String, +s: String, +n: Nat, +x: U32, +b: Bool, +a: String, +xs: List<&2, Nat>, pre: {s == Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, LawsBase.wire_spell_nats(xs, r))))) : String}, f: {WireFfi.wr_fits(WireFfi.wr.Req{n, x, b, a, xs}) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FWi.at.end(Wr.Got{xs, r}, n, x, b, a)) == False{} : Bool}) -> ro.G(s, FWi.at.end(Wr.Got{xs, r}, n, x, b, a)):
  match r:
    case SNil{}:
      (WireFfi.wr.Req{n, x, b, a, xs}, ro.top(s, WireFfi.wr.Req{n, x, b, a, xs}, FWi.at.end(Wr.Got{xs, ""}, n, x, b, a), pre, f, LA.wrb.spell(n, x, b, a, xs, "")))
    case SCon{c, t}:
      LAWireSpell.ws_absurd(ro.G(s, FWi.bad()), ok)

def ro.list(+s: String, +n: Nat, +x: U32, +b: Bool, +a: String, +s4: String, pre: {s == Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, s4)))) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s4) == d : Wr.Dec<List<&2, Nat>>}, ok: {LawsBase.wire_opens_err(FWi.at.end(d, n, x, b, a)) == False{} : Bool}) -> ro.G(s, FWi.at.end(d, n, x, b, a)):
  match d:
    case Wr.Got{+xs, +r}:
      +ee = ed
      +e4 = Equal.trans(String, s4, Wr.put_list(~Nat, ~Wr.put_nat, xs, r), LawsBase.wire_spell_nats(xs, r), Wire.wire_list_exact(s4, xs, r, ee), Wire.wire_nats_spells(xs, r))
      +fl = LA.wrb.nats_fit(s4, xs, r, ee)
      ro.fin(r, s, n, x, b, a, xs, LA.wrb.step(z => Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, z)))), s, s4, LawsBase.wire_spell_nats(xs, r), pre, e4), LAWireSpell.ws_and_tt(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))), fn, LAWireSpell.ws_and_tt(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), fa, fl)), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, FWi.bad()), ok)

def ro.str(+s: String, +n: Nat, +x: U32, +b: Bool, +s3: String, pre: {s == Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, s3))) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<String>, ed: {Wr.get_str(s3) == d : Wr.Dec<String>}, ok: {LawsBase.wire_opens_err(FWi.at.str(d, n, x, b)) == False{} : Bool}) -> ro.G(s, FWi.at.str(d, n, x, b)):
  match d:
    case Wr.Got{+a, +s4}:
      +ee = ed
      ro.list(s, n, x, b, a, s4, LA.wrb.step(z => Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, z))), s, s3, Wr.put_str(a, s4), pre, Wire.wire_str_exact(s3, a, s4, ee)), fn, Wire.wire_str_decoded_fits(s3, a, s4, ee), Wr.get_list(~Nat, ~Wr.get_nat, s4), {==}, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, FWi.bad()), ok)

def ro.bool(+s: String, +n: Nat, +x: U32, +s2: String, pre: {s == Wr.put_nat(n, Wr.put_u32(x, s2)) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}, ok: {LawsBase.wire_opens_err(FWi.at.bool(d, n, x)) == False{} : Bool}) -> ro.G(s, FWi.at.bool(d, n, x)):
  match d:
    case Wr.Got{+b, +s3}:
      ro.str(s, n, x, b, s3, LA.wrb.step(z => Wr.put_nat(n, Wr.put_u32(x, z)), s, s2, Wr.put_bool(b, s3), pre, Wire.wire_bool_exact(s2, b, s3, ed)), fn, Wr.get_str(s3), {==}, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, FWi.bad()), ok)

def ro.u32(+s: String, +n: Nat, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<U32>, ed: {Wr.get_u32(s1) == d : Wr.Dec<U32>}, ok: {LawsBase.wire_opens_err(FWi.at.u32(d, n)) == False{} : Bool}) -> ro.G(s, FWi.at.u32(d, n)):
  match d:
    case Wr.Got{+x, +s2}:
      ro.bool(s, n, x, s2, LA.wrb.step(z => Wr.put_nat(n, z), s, s1, Wr.put_u32(x, s2), pre, Wire.wire_u32_exact(s1, x, s2, ed)), fn, Wr.get_bool(s2), {==}, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, FWi.bad()), ok)

def ro.nat(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FWi.at.nat(d)) == False{} : Bool}) -> ro.G(s, FWi.at.nat(d)):
  match d:
    case Wr.Got{+n, +s1}:
      +ee = ed
      ro.u32(s, n, s1, Wire.wire_nat_exact(s, n, s1, ee), Wire.wire_nat_decoded_fits(s, n, s1, ee), Wr.get_u32(s1), {==}, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, FWi.bad()), ok)

def WireFfi.wire_ffi_reads_only_requests(s, ok):
  ro.nat(s, Wr.get_nat(s), {==}, ok)
