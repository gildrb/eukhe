# eukhe: exactness of the request decoder of bend/ffi_aux_fallback.bend:
# whatever a decoder reads is the grammar's spelling of what it read
# (laws/aux_fallback.bend afw_spell_*), then its rest, and every number of
# it fits the wire (used by afw_reads_only_requests and
# afw_malformed_unless_request)

import Base
import ../../../bend/aux_fallback.bend as Af
import ../../../bend/ffi_aux_fallback.bend as FAf
import ../../../bend/wire.bend as Wr
import ../../../laws/aux_fallback/wire.bend as AuxFallbackWire
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/base/spell.bend as LAWireSpell

# s spelled up to a field a is s spelled up to its spelling b
def afx.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# ---- Nat, Bool ----

def afx.PN(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def afx.nat.go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> afx.PN(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

# every Nat the decoder reads is spelled and fits
def afx.nat(+s: String) -> afx.PN(s, Wr.get_nat(s)):
  afx.nat.go(s, Wr.get_nat(s), {==})

def afx.PB(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def afx.bool.go(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> afx.PB(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

# every Bool the decoder reads is spelled
def afx.bool(+s: String) -> afx.PB(s, Wr.get_bool(s)):
  afx.bool.go(s, Wr.get_bool(s), {==})

# ---- Key ----

def afx.PK(s: String, d: Wr.Dec<Af.Key>) -> Type:
  match d:
    case Wr.Got{+k, r}:
      {s == AuxFallbackWire.afw_spell_key(k, r) : String} & {AuxFallbackWire.afw_key_fits(k) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def afx.key.r(-s: String, +p: Nat, +q: Nat, -s2: String, pre: {s == Wr.put_nat(p, Wr.put_nat(q, s2)) : String}, fp: {LawsBase.wire_fits(p) == True{} : Bool}, fq: {LawsBase.wire_fits(q) == True{} : Bool}, d: Wr.Dec<Nat>, pn: afx.PN(s2, d)) -> afx.PK(s, FAf.get_key.r(p, q, d)):
  match d:
    case Wr.Got{+r, +s3}:
      (er, fr) = pn
      (afx.step(z => Wr.put_nat(p, Wr.put_nat(q, z)), s, s2, Wr.put_nat(r, s3), pre, er), LAWireSpell.ws_and_tt(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(q), LawsBase.wire_fits(r)), fp, LAWireSpell.ws_and_tt(LawsBase.wire_fits(q), LawsBase.wire_fits(r), fq, fr)))
    case Wr.Bad{}:
      Unit{}

def afx.key.s(-s: String, +p: Nat, -s1: String, pre: {s == Wr.put_nat(p, s1) : String}, fp: {LawsBase.wire_fits(p) == True{} : Bool}, d: Wr.Dec<Nat>, pn: afx.PN(s1, d)) -> afx.PK(s, FAf.get_key.s(p, d)):
  match d:
    case Wr.Got{+q, +s2}:
      (eq, fq) = pn
      afx.key.r(s, p, q, s2, afx.step(z => Wr.put_nat(p, z), s, s1, Wr.put_nat(q, s2), pre, eq), fp, fq, Wr.get_nat(s2), afx.nat(s2))
    case Wr.Bad{}:
      Unit{}

def afx.key.go(-s: String, d: Wr.Dec<Nat>, pn: afx.PN(s, d)) -> afx.PK(s, FAf.get_key.go(d)):
  match d:
    case Wr.Got{+p, +s1}:
      (ep, fp) = pn
      afx.key.s(s, p, s1, ep, fp, Wr.get_nat(s1), afx.nat(s1))
    case Wr.Bad{}:
      Unit{}

# every key the decoder reads is spelled and fits
def afx.key(+s: String) -> afx.PK(s, FAf.get_key(s)):
  afx.key.go(s, Wr.get_nat(s), afx.nat(s))

# ---- Route ----

def afx.PR(s: String, d: Wr.Dec<Af.Route>) -> Type:
  match d:
    case Wr.Got{+r, x}:
      {s == AuxFallbackWire.afw_spell_route(r, x) : String} & {AuxFallbackWire.afw_route_fits(r) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def afx.route.fb(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Af.Key>, pk: afx.PK(s1, d)) -> afx.PR(s, FAf.get_route.fallback(d)):
  match d:
    case Wr.Got{+k, +s2}:
      (ek, fk) = pk
      (afx.step(z => Wr.put_nat(2n, z), s, s1, AuxFallbackWire.afw_spell_key(k, s2), pre, ek), fk)
    case Wr.Bad{}:
      Unit{}

def afx.route.go(-s: String, d: Wr.Dec<Nat>, pn: afx.PN(s, d)) -> afx.PR(s, FAf.get_route.go(d)):
  match d:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          (en, fn) = pn
          (en, {==})
        case 1n:
          (en, fn) = pn
          (en, {==})
        case 2n:
          (en, fn) = pn
          afx.route.fb(s, s1, en, FAf.get_key(s1), afx.key(s1))
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every route the decoder reads is spelled and fits
def afx.route(+s: String) -> afx.PR(s, FAf.get_route(s)):
  afx.route.go(s, Wr.get_nat(s), afx.nat(s))

# ---- Gate ----

def afx.PG(s: String, d: Wr.Dec<Af.Gate>) -> Type:
  match d:
    case Wr.Got{+g, x}:
      {s == AuxFallbackWire.afw_spell_gate(g, x) : String} & {AuxFallbackWire.afw_gate_fits(g) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def afx.gate.known(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Af.Route>, pr: afx.PR(s1, d)) -> afx.PG(s, FAf.get_gate.known(d)):
  match d:
    case Wr.Got{+r, +s2}:
      (er, fr) = pr
      (afx.step(z => Wr.put_nat(0n, z), s, s1, AuxFallbackWire.afw_spell_route(r, s2), pre, er), fr)
    case Wr.Bad{}:
      Unit{}

def afx.gate.s(-s: String, +p: Nat, -s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(p, s2)) : String}, fp: {LawsBase.wire_fits(p) == True{} : Bool}, d: Wr.Dec<Nat>, pn: afx.PN(s2, d)) -> afx.PG(s, FAf.get_gate.s(p, d)):
  match d:
    case Wr.Got{+q, +s3}:
      (eq, fq) = pn
      (afx.step(z => Wr.put_nat(1n, Wr.put_nat(p, z)), s, s2, Wr.put_nat(q, s3), pre, eq), LAWireSpell.ws_and_tt(LawsBase.wire_fits(p), LawsBase.wire_fits(q), fp, fq))
    case Wr.Bad{}:
      Unit{}

def afx.gate.p(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, pn: afx.PN(s1, d)) -> afx.PG(s, FAf.get_gate.p(d)):
  match d:
    case Wr.Got{+p, +s2}:
      (ep, fp) = pn
      afx.gate.s(s, p, s2, afx.step(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(p, s2), pre, ep), fp, Wr.get_nat(s2), afx.nat(s2))
    case Wr.Bad{}:
      Unit{}

def afx.gate.go(-s: String, d: Wr.Dec<Nat>, pn: afx.PN(s, d)) -> afx.PG(s, FAf.get_gate.go(d)):
  match d:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          (en, fn) = pn
          afx.gate.known(s, s1, en, FAf.get_route(s1), afx.route(s1))
        case 1n:
          (en, fn) = pn
          afx.gate.p(s, s1, en, Wr.get_nat(s1), afx.nat(s1))
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every gate the decoder reads is spelled and fits
def afx.gate(+s: String) -> afx.PG(s, FAf.get_gate(s)):
  afx.gate.go(s, Wr.get_nat(s), afx.nat(s))

# ---- Sel ----

def afx.PS(s: String, d: Wr.Dec<Af.Sel>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == AuxFallbackWire.afw_spell_sel(x, r) : String} & {AuxFallbackWire.afw_sel_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def afx.sel.other(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, pn: afx.PN(s1, d)) -> afx.PS(s, FAf.get_sel.other(d)):
  match d:
    case Wr.Got{+q, +s2}:
      (eq, fq) = pn
      (afx.step(z => Wr.put_nat(2n, z), s, s1, Wr.put_nat(q, s2), pre, eq), fq)
    case Wr.Bad{}:
      Unit{}

def afx.sel.go(-s: String, d: Wr.Dec<Nat>, pn: afx.PN(s, d)) -> afx.PS(s, FAf.get_sel.go(d)):
  match d:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          (en, fn) = pn
          (en, {==})
        case 1n:
          (en, fn) = pn
          (en, {==})
        case 2n:
          (en, fn) = pn
          afx.sel.other(s, s1, en, Wr.get_nat(s1), afx.nat(s1))
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every selector the decoder reads is spelled and fits
def afx.sel(+s: String) -> afx.PS(s, FAf.get_sel(s)):
  afx.sel.go(s, Wr.get_nat(s), afx.nat(s))

# ---- Look ----

def afx.PL(s: String, d: Wr.Dec<Af.Look>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == AuxFallbackWire.afw_spell_look(x, r) : String} & {AuxFallbackWire.afw_look_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def afx.look.miss(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, pn: afx.PN(s1, d)) -> afx.PL(s, FAf.get_look.tag(d, 0n)):
  match d:
    case Wr.Got{+x, +s2}:
      (ex, fx) = pn
      (afx.step(z => Wr.put_nat(0n, z), s, s1, Wr.put_nat(x, s2), pre, ex), fx)
    case Wr.Bad{}:
      Unit{}

def afx.look.hit(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, pn: afx.PN(s1, d)) -> afx.PL(s, FAf.get_look.tag(d, 1n)):
  match d:
    case Wr.Got{+x, +s2}:
      (ex, fx) = pn
      (afx.step(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(x, s2), pre, ex), fx)
    case Wr.Bad{}:
      Unit{}

def afx.look.go(-s: String, d: Wr.Dec<Nat>, pn: afx.PN(s, d)) -> afx.PL(s, FAf.get_look.go(d)):
  match d:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          (en, fn) = pn
          afx.look.miss(s, s1, en, Wr.get_nat(s1), afx.nat(s1))
        case 1n:
          (en, fn) = pn
          afx.look.hit(s, s1, en, Wr.get_nat(s1), afx.nat(s1))
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every lookup result the decoder reads is spelled and fits
def afx.look(+s: String) -> afx.PL(s, FAf.get_look(s)):
  afx.look.go(s, Wr.get_nat(s), afx.nat(s))

# ---- List<Key> ----

# what the item loop's answer says about its input s (m + 1 keys)
def afx.PLL(s: String, m: Nat, d: Wr.Dec<List<&2, Af.Key>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == AuxFallbackWire.afw_spell_key_items(xs, r) : String} & ({List.length(&2, Af.Key, xs) == 1n+m : Nat} & {AuxFallbackWire.afw_keys_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

# one more spelled key before the rest of the loop
def afx.keys.step(-s: String, +x: Af.Key, -s3: String, -k: Nat, ex: {s == AuxFallbackWire.afw_spell_key(x, s3) : String}, fx: {AuxFallbackWire.afw_key_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Af.Key>>, ih: afx.PLL(s3, k, d)) -> afx.PLL(s, 1n+k, Wr.get_list.cons(Af.Key, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (afx.step(z => AuxFallbackWire.afw_spell_key(x, z), s, s3, AuxFallbackWire.afw_spell_key_items(ys, r), ex, e1),
        (Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Af.Key, ys), 1n+k, e2),
          LAWireSpell.ws_and_tt(AuxFallbackWire.afw_key_fits(x), AuxFallbackWire.afw_keys_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled keys that fit
def afx.keys.loop(m: Nat, cur: Wr.Dec<Af.Key>, +s: String, pc: afx.PK(s, cur)) ->
  afx.PLL(s, m, Wr.get_list.go(~Af.Key, ~FAf.get_key, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, s3}:
      (ex, fx) = pc
      (ex, ({==}, LAWireSpell.ws_and_tt(AuxFallbackWire.afw_key_fits(x), True{}, fx, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (ex, fx) = pc
      afx.keys.step(s, x, s3, k, ex, fx, Wr.get_list.go(~Af.Key, ~FAf.get_key, k, FAf.get_key(s3)),
        afx.keys.loop(k, FAf.get_key(s3), s3, afx.key(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list-of-keys decoder's answer says about its input s
def afx.PKL(s: String, d: Wr.Dec<List<&2, Af.Key>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == AuxFallbackWire.afw_spell_keys(xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Af.Key, xs)), AuxFallbackWire.afw_keys_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the count spelled before the keys is the list's length
def afx.keys.eq(-s: String, -s2: String, -m: Nat, +xs: List<&2, Af.Key>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == AuxFallbackWire.afw_spell_key_items(xs, r) : String},
  e2: {List.length(&2, Af.Key, xs) == 1n+m : Nat}) -> {s == AuxFallbackWire.afw_spell_keys(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, Af.Key, xs), 1n+m, e2) : {s == Wr.put_nat(_, AuxFallbackWire.afw_spell_key_items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

# m + 1 spelled keys after their count: a spelled list that fits
def afx.keys.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Af.Key>>, pl: afx.PLL(s2, m, d)) -> afx.PKL(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (afx.keys.eq(s, s2, m, xs, r, en, e1, e2),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Af.Key, xs)), AuxFallbackWire.afw_keys_fit(xs),
          Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Af.Key, xs)), LawsBase.wire_fits(1n+m), True{},
            Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, Af.Key, xs), 1n+m, e2), fn), e3))
    case Wr.Bad{}:
      Unit{}

# the count 0 is the empty list; else the item loop runs
def afx.keys.nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> afx.PKL(s, Wr.get_list.start(~Af.Key, ~FAf.get_key, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      afx.keys.conv(s, s2, m, en, fn, Wr.get_list.go(~Af.Key, ~FAf.get_key, m, FAf.get_key(s2)),
        afx.keys.loop(m, FAf.get_key(s2), s2, afx.key(s2)))

def afx.keys.top(+s: String, d: Wr.Dec<Nat>, pn: afx.PN(s, d)) -> afx.PKL(s, Wr.get_list.start(~Af.Key, ~FAf.get_key, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = pn
      afx.keys.nat(s, n, s2, en, fn)
    case Wr.Bad{}:
      Unit{}

# every list of keys the decoder reads is spelled and fits
def afx.keys(+s: String) -> afx.PKL(s, Wr.get_list(~Af.Key, ~FAf.get_key, s)):
  afx.keys.top(s, Wr.get_nat(s), afx.nat(s))

# ---- Req ----

# the request: its spelling, then its rest, and it fits
def afx.PQ(s: String, d: Wr.Dec<FAf.Req>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == AuxFallbackWire.afw_spell_req(x, r) : String} & {AuxFallbackWire.afw_req_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def afx.req.ok(-s: String, +p: Nat, +sel: Af.Sel, -s3: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(p, AuxFallbackWire.afw_spell_sel(sel, s3))) : String},
  f: {Bool.and(LawsBase.wire_fits(p), AuxFallbackWire.afw_sel_fits(sel)) == True{} : Bool}, d: Wr.Dec<Bool>, pb: afx.PB(s3, d)) -> afx.PQ(s, FAf.get_req.ok(p, sel, d)):
  match d:
    case Wr.Got{+ok, +s4}:
      (afx.step(z => Wr.put_nat(0n, Wr.put_nat(p, AuxFallbackWire.afw_spell_sel(sel, z))), s, s3, Wr.put_bool(ok, s4), pre, pb), f)
    case Wr.Bad{}:
      Unit{}

def afx.req.sel(-s: String, +p: Nat, -s2: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(p, s2)) : String}, fp: {LawsBase.wire_fits(p) == True{} : Bool},
  d: Wr.Dec<Af.Sel>, ps: afx.PS(s2, d)) -> afx.PQ(s, FAf.get_req.sel(p, d)):
  match d:
    case Wr.Got{+sel, +s3}:
      (es, fs) = ps
      afx.req.ok(s, p, sel, s3, afx.step(z => Wr.put_nat(0n, Wr.put_nat(p, z)), s, s2, AuxFallbackWire.afw_spell_sel(sel, s3), pre, es),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(p), AuxFallbackWire.afw_sel_fits(sel), fp, fs), Wr.get_bool(s3), afx.bool(s3))
    case Wr.Bad{}:
      Unit{}

def afx.req.gate(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, pn: afx.PN(s1, d)) -> afx.PQ(s, FAf.get_req.gate(d)):
  match d:
    case Wr.Got{+p, +s2}:
      (ep, fp) = pn
      afx.req.sel(s, p, s2, afx.step(z => Wr.put_nat(0n, z), s, s1, Wr.put_nat(p, s2), pre, ep), fp, FAf.get_sel(s2), afx.sel(s2))
    case Wr.Bad{}:
      Unit{}

def afx.req.need(-s: String, +g: Af.Gate, +look: Af.Look, -s3: String, pre: {s == Wr.put_nat(1n, AuxFallbackWire.afw_spell_gate(g, AuxFallbackWire.afw_spell_look(look, s3))) : String},
  fg: {AuxFallbackWire.afw_gate_fits(g) == True{} : Bool}, fl: {AuxFallbackWire.afw_look_fits(look) == True{} : Bool}, d: Wr.Dec<Nat>, pn: afx.PN(s3, d)) -> afx.PQ(s, FAf.get_req.need(g, look, d)):
  match d:
    case Wr.Got{+need, +s4}:
      (en, fn) = pn
      (afx.step(z => Wr.put_nat(1n, AuxFallbackWire.afw_spell_gate(g, AuxFallbackWire.afw_spell_look(look, z))), s, s3, Wr.put_nat(need, s4), pre, en),
        LAWireSpell.ws_and_tt(AuxFallbackWire.afw_gate_fits(g), Bool.and(AuxFallbackWire.afw_look_fits(look), LawsBase.wire_fits(need)), fg,
          LAWireSpell.ws_and_tt(AuxFallbackWire.afw_look_fits(look), LawsBase.wire_fits(need), fl, fn)))
    case Wr.Bad{}:
      Unit{}

def afx.req.look(-s: String, +g: Af.Gate, -s2: String, pre: {s == Wr.put_nat(1n, AuxFallbackWire.afw_spell_gate(g, s2)) : String}, fg: {AuxFallbackWire.afw_gate_fits(g) == True{} : Bool},
  d: Wr.Dec<Af.Look>, pl: afx.PL(s2, d)) -> afx.PQ(s, FAf.get_req.look(g, d)):
  match d:
    case Wr.Got{+look, +s3}:
      (el, fl) = pl
      afx.req.need(s, g, look, s3, afx.step(z => Wr.put_nat(1n, AuxFallbackWire.afw_spell_gate(g, z)), s, s2, AuxFallbackWire.afw_spell_look(look, s3), pre, el), fg, fl, Wr.get_nat(s3), afx.nat(s3))
    case Wr.Bad{}:
      Unit{}

def afx.req.settle(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Af.Gate>, pg: afx.PG(s1, d)) -> afx.PQ(s, FAf.get_req.settle(d)):
  match d:
    case Wr.Got{+g, +s2}:
      (eg, fg) = pg
      afx.req.look(s, g, s2, afx.step(z => Wr.put_nat(1n, z), s, s1, AuxFallbackWire.afw_spell_gate(g, s2), pre, eg), fg, FAf.get_look(s2), afx.look(s2))
    case Wr.Bad{}:
      Unit{}

def afx.req.shown(-s: String, +r: Af.Route, -s2: String, pre: {s == Wr.put_nat(2n, AuxFallbackWire.afw_spell_route(r, s2)) : String}, fr: {AuxFallbackWire.afw_route_fits(r) == True{} : Bool},
  d: Wr.Dec<List<&2, Af.Key>>, pk: afx.PKL(s2, d)) -> afx.PQ(s, FAf.get_req.shown(r, d)):
  match d:
    case Wr.Got{+sh, +s3}:
      (ek, fk) = pk
      (afx.step(z => Wr.put_nat(2n, AuxFallbackWire.afw_spell_route(r, z)), s, s2, AuxFallbackWire.afw_spell_keys(sh, s3), pre, ek),
        LAWireSpell.ws_and_tt(AuxFallbackWire.afw_route_fits(r), Bool.and(LawsBase.wire_fits(List.length(&2, Af.Key, sh)), AuxFallbackWire.afw_keys_fit(sh)), fr, fk))
    case Wr.Bad{}:
      Unit{}

def afx.req.pass(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Af.Route>, pr: afx.PR(s1, d)) -> afx.PQ(s, FAf.get_req.pass(d)):
  match d:
    case Wr.Got{+r, +s2}:
      (er, fr) = pr
      afx.req.shown(s, r, s2, afx.step(z => Wr.put_nat(2n, z), s, s1, AuxFallbackWire.afw_spell_route(r, s2), pre, er), fr, Wr.get_list(~Af.Key, ~FAf.get_key, s2), afx.keys(s2))
    case Wr.Bad{}:
      Unit{}

def afx.req.go(-s: String, d: Wr.Dec<Nat>, pn: afx.PN(s, d)) -> afx.PQ(s, FAf.get_req.go(d)):
  match d:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          (en, fn) = pn
          afx.req.gate(s, s1, en, Wr.get_nat(s1), afx.nat(s1))
        case 1n:
          (en, fn) = pn
          afx.req.settle(s, s1, en, FAf.get_gate(s1), afx.gate(s1))
        case 2n:
          (en, fn) = pn
          afx.req.pass(s, s1, en, FAf.get_route(s1), afx.route(s1))
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def afx.req(+s: String) -> afx.PQ(s, FAf.get_req(s)):
  afx.req.go(s, Wr.get_nat(s), afx.nat(s))
