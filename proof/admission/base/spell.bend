# eukhe: lemmas the proofs of area admission share: the stepper's bytes
# spelled (laws/admission.bend, section admission_stepper)
#
# asp.<x>: the entry's encoder of x is its laws-side spelling (tag by
# tag, the ticket list by induction). asx.<x>: whatever the entry's
# decoder of x reads is the spelling of what it read, then its rest, and
# it fits the wire (tag by tag with the wire's exactness laws; an unknown
# tag is Bad). asx.Open / asx.Op carry this for the two requests.

import Base
import ../../../bend/admission.bend as Ad
import ../../../bend/ffi_admission.bend as FAd
import ../../../bend/wire.bend as Wr
import ../../../laws/admission.bend as Admission
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/base/spell.bend as LAWireSpell

# Encoders: the entry's is the spelling
# -------------------------------------

def asp.cls(c: Ad.Cls, -rest: String) -> {FAd.put_cls(c, rest) == Admission.adw_spell_cls(c, rest) : String}:
  match c:
    case Ad.Ia{}:
      {==}
    case Ad.Bg{}:
      {==}

def asp.sts(s: Ad.Sts, -rest: String) -> {FAd.put_sts(s, rest) == Admission.adw_spell_sts(s, rest) : String}:
  match s:
    case Ad.Queued{}:
      {==}
    case Ad.Granted{}:
      {==}
    case Ad.Held{}:
      {==}
    case Ad.Preempted{}:
      {==}
    case Ad.Ended{}:
      {==}

def asp.lim(l: Ad.Lim, -rest: String) -> {FAd.put_lim(l, rest) == Admission.adw_spell_lim(l, rest) : String}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      {==}

def asp.op(o: Ad.Op, -rest: String) -> {FAd.put_op(o, rest) == Admission.adw_spell_op(o, rest) : String}:
  match o:
    case Ad.Admit{+c}:
      %asp.cls(c, rest) : {Wr.put_nat(0n, FAd.put_cls(c, rest)) == Wr.put_nat(0n, _) : String}
      {==}
    case Ad.Collect{k}:
      {==}
    case Ad.Release{k}:
      {==}
    case Ad.Depart{k}:
      {==}
    case Ad.Limit{+l, +q}:
      %asp.lim(l, Wr.put_nat(q, rest)) : {Wr.put_nat(4n, FAd.put_lim(l, Wr.put_nat(q, rest))) == Wr.put_nat(4n, _) : String}
      {==}

def asp.lv(t: Ad.Lv, -rest: String) -> {FAd.put_lv(t, rest) == Admission.adw_spell_lv(t, rest) : String}:
  match t:
    case Ad.Lv{+k, +c, +s}:
      %asp.sts(s, rest) : {Wr.put_nat(k, FAd.put_cls(c, FAd.put_sts(s, rest))) == Wr.put_nat(k, Admission.adw_spell_cls(c, _)) : String}
      %asp.cls(c, FAd.put_sts(s, rest)) : {Wr.put_nat(k, FAd.put_cls(c, FAd.put_sts(s, rest))) == Wr.put_nat(k, _) : String}
      {==}

# put_list's loop over the tickets: the count and the spelled tickets
def asp.lvs_go(ts: List<&2, Ad.Lv>, -rest: String) -> {Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, ts, rest) == (List.length(&2, Ad.Lv, ts), Admission.adw_spell_lvs.items(ts, rest)) : Nat & String}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +u}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, u, rest), (List.length(&2, Ad.Lv, u), Admission.adw_spell_lvs.items(u, rest)), asp.lvs_go(u, rest)) : {Wr.put_list.step(~Ad.Lv, ~FAd.put_lv, t, _) == (1n+List.length(&2, Ad.Lv, u), Admission.adw_spell_lv(t, Admission.adw_spell_lvs.items(u, rest))) : Nat & String}
      %asp.lv(t, Admission.adw_spell_lvs.items(u, rest)) : {(1n+List.length(&2, Ad.Lv, u), FAd.put_lv(t, Admission.adw_spell_lvs.items(u, rest))) == (1n+List.length(&2, Ad.Lv, u), _) : Nat & String}
      {==}

def asp.live(x: Ad.Live, -rest: String) -> {FAd.put_live(x, rest) == Admission.adw_spell_live(x, rest) : String}:
  match x:
    case Ad.Live{+l, +q, +ts, +n}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, ts, Wr.put_nat(n, rest)), (List.length(&2, Ad.Lv, ts), Admission.adw_spell_lvs.items(ts, Wr.put_nat(n, rest))), asp.lvs_go(ts, Wr.put_nat(n, rest))) : {FAd.put_lim(l, Wr.put_nat(q, Wr.put_list.fin(_))) == Admission.adw_spell_lim(l, Wr.put_nat(q, Admission.adw_spell_lvs(ts, Wr.put_nat(n, rest)))) : String}
      %asp.lim(l, Wr.put_nat(q, Admission.adw_spell_lvs(ts, Wr.put_nat(n, rest)))) : {FAd.put_lim(l, Wr.put_nat(q, Admission.adw_spell_lvs(ts, Wr.put_nat(n, rest)))) == _ : String}
      {==}

# a reply that is a controller never opens with 'E'
def asp.live_not_err(x: Ad.Live, -rest: String) -> {LawsBase.wire_opens_err(FAd.put_live(x, rest)) == False{} : Bool}:
  match x:
    case Ad.Live{l, q, ts, n}:
      match l:
        case Ad.Unl{}:
          {==}
        case Ad.Cap{p}:
          {==}

# False is not True
def asp.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  LAWireSpell.ws_absurd(G, Equal.sym(Bool, False{}, True{}, e))

# s spelled up to a field a is s spelled up to its spelling b
def asx.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# Decoders: what each read is its spelling, then its rest, and fits
# -----------------------------------------------------------------

def asx.Cls(s: String, d: Wr.Dec<Ad.Cls>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == Admission.adw_spell_cls(c, r) : String}
    case Wr.Bad{}:
      Unit

def asx.cls.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> asx.Cls(s, FAd.get_cls.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def asx.cls(+s: String) -> asx.Cls(s, FAd.get_cls(s)):
  asx.cls.go(s, Wr.get_nat(s), {==})

def asx.Lim(s: String, d: Wr.Dec<Ad.Lim>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Admission.adw_spell_lim(l, r) : String} & {Admission.adw_lim_fits(l) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def asx.lim.cap(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> asx.Lim(s, FAd.get_lim.cap(d)):
  match d:
    case Wr.Got{+p, +s1}:
      +ee = ed
      (asx.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(p, s1), pre, Wire.wire_nat_exact(s0, p, s1, ee)), Wire.wire_nat_decoded_fits(s0, p, s1, ee))
    case Wr.Bad{}:
      Unit{}

def asx.lim.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> asx.Lim(s, FAd.get_lim.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n:
          asx.lim.cap(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def asx.lim(+s: String) -> asx.Lim(s, FAd.get_lim(s)):
  asx.lim.go(s, Wr.get_nat(s), {==})

# The open request
# ----------------

def asx.Open.at(s: String, lq: +Sigma<Ad.Lim, x => Nat>, r: String) -> Type:
  match lq:
    case (l, q):
      {s == Admission.adw_spell_open(l, q, r) : String} & {Bool.and(Admission.adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}

def asx.Open(s: String, d: Wr.Dec<+Sigma<Ad.Lim, x => Nat>>) -> Type:
  match d:
    case Wr.Got{lq, r}:
      asx.Open.at(s, lq, r)
    case Wr.Bad{}:
      Unit

def asx.open.q(+s: String, +l: Ad.Lim, +s1: String, pre: {s == Admission.adw_spell_lim(l, s1) : String}, fl: {Admission.adw_lim_fits(l) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> asx.Open(s, FAd.get_open.q(l, d)):
  match d:
    case Wr.Got{+q, +s2}:
      +ee = ed
      (asx.step(z => Admission.adw_spell_lim(l, z), s, s1, Wr.put_nat(q, s2), pre, Wire.wire_nat_exact(s1, q, s2, ee)), LAWireSpell.ws_and_tt(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), fl, Wire.wire_nat_decoded_fits(s1, q, s2, ee)))
    case Wr.Bad{}:
      Unit{}

def asx.open.go(+s: String, d: Wr.Dec<Ad.Lim>, xd: asx.Lim(s, d)) -> asx.Open(s, FAd.get_open.go(d)):
  match d:
    case Wr.Got{+l, +s1}:
      (e1, fl) = xd
      asx.open.q(s, l, s1, e1, fl, Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# whatever the entry reads as an open is a spelled open that fits, then
# the rest
def asx.open(+s: String) -> asx.Open(s, FAd.get_open(s)):
  asx.open.go(s, FAd.get_lim(s), asx.lim(s))

# The op request
# --------------

def asx.Op(s: String, d: Wr.Dec<Ad.Op>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == Admission.adw_spell_op(o, r) : String} & {Admission.adw_op_fits(o) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def asx.op.admit(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Ad.Cls>, xd: asx.Cls(s0, d)) -> asx.Op(s, FAd.get_op.admit(d)):
  match d:
    case Wr.Got{+c, +s1}:
      (asx.step(z => Wr.put_nat(0n, z), s, s0, Admission.adw_spell_cls(c, s1), pre, xd), {==})
    case Wr.Bad{}:
      Unit{}

def asx.op.collect(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> asx.Op(s, FAd.get_op.k(d, 0n)):
  match d:
    case Wr.Got{+k, +s1}:
      +ee = ed
      (asx.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(k, s1), pre, Wire.wire_nat_exact(s0, k, s1, ee)), Wire.wire_nat_decoded_fits(s0, k, s1, ee))
    case Wr.Bad{}:
      Unit{}

def asx.op.release(+s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> asx.Op(s, FAd.get_op.k(d, 1n)):
  match d:
    case Wr.Got{+k, +s1}:
      +ee = ed
      (asx.step(z => Wr.put_nat(2n, z), s, s0, Wr.put_nat(k, s1), pre, Wire.wire_nat_exact(s0, k, s1, ee)), Wire.wire_nat_decoded_fits(s0, k, s1, ee))
    case Wr.Bad{}:
      Unit{}

def asx.op.leave(+s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> asx.Op(s, FAd.get_op.k(d, 2n)):
  match d:
    case Wr.Got{+k, +s1}:
      +ee = ed
      (asx.step(z => Wr.put_nat(3n, z), s, s0, Wr.put_nat(k, s1), pre, Wire.wire_nat_exact(s0, k, s1, ee)), Wire.wire_nat_decoded_fits(s0, k, s1, ee))
    case Wr.Bad{}:
      Unit{}

def asx.op.q(+s: String, +l: Ad.Lim, +s1: String, pre: {s == Wr.put_nat(4n, Admission.adw_spell_lim(l, s1)) : String}, fl: {Admission.adw_lim_fits(l) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> asx.Op(s, FAd.get_op.q(l, d)):
  match d:
    case Wr.Got{+q, +s2}:
      +ee = ed
      (asx.step(z => Wr.put_nat(4n, Admission.adw_spell_lim(l, z)), s, s1, Wr.put_nat(q, s2), pre, Wire.wire_nat_exact(s1, q, s2, ee)), LAWireSpell.ws_and_tt(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), fl, Wire.wire_nat_decoded_fits(s1, q, s2, ee)))
    case Wr.Bad{}:
      Unit{}

def asx.op.limit(+s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<Ad.Lim>, xd: asx.Lim(s0, d)) -> asx.Op(s, FAd.get_op.limit(d)):
  match d:
    case Wr.Got{+l, +s1}:
      (e1, fl) = xd
      asx.op.q(s, l, s1, asx.step(z => Wr.put_nat(4n, z), s, s0, Admission.adw_spell_lim(l, s1), pre, e1), fl, Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def asx.op.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> asx.Op(s, FAd.get_op.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          asx.op.admit(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FAd.get_cls(s0), asx.cls(s0))
        case 1n:
          asx.op.collect(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n:
          asx.op.release(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_nat(s0), {==})
        case 3n:
          asx.op.leave(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_nat(s0), {==})
        case 4n:
          asx.op.limit(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), FAd.get_lim(s0), asx.lim(s0))
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the entry reads as an op is a spelled op that fits, then the
# rest
def asx.op(+s: String) -> asx.Op(s, FAd.get_op(s)):
  asx.op.go(s, Wr.get_nat(s), {==})
