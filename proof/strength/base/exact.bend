# eukhe: lemmas of the entry proofs of area strength
# (bend/ffi_strength.bend): the request decoder answers Got{q, rest} only
# for an input that is the spelling of q before rest, every number and
# count within the wire (sx.req). Per decoder, a predicate on its answer
# (what it says about its input), carried stage by stage on the wire's
# exactness laws wire_nat_exact, wire_nat_decoded_fits, wire_bool_exact and
# wire_list_reads_items; the gauges and the slots item by item. No answer
# of the entry to a request opens with 'E' (sx.answer_ok). The attack
# entry reads verify's label, the gauges and the slots with the same
# decoders and uses these lemmas too.

import Base
import ../../../bend/verify.bend as V
import ../../../bend/strength.bend as St
import ../../../bend/ffi_verify.bend as FV
import ../../../bend/ffi_strength.bend as FS
import ../../../bend/wire.bend as Wr
import ../../../spec/verified/verify_wire.bend as SVW
import ../../../spec/verified/strength_wire.bend as SSW
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ../../verify/base/entry.bend as LVE
import ./entry.bend as LSE

# s is P(a), and a is b: s is P(b)
def sx.ext(P: String -> String, -s: String, -a: String, -b: String, pre: {s == P(a) : String}, e: {a == b : String}) -> {s == P(b) : String}:
  Equal.trans(String, s, P(a), P(b), pre, Equal.cong(String, String, P, a, b, e))

def sx.and_t(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def sx.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# a premise True == False proves anything
def sx.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : sx.BD(_, Unit, A)
  Unit{}

# Numbers, Bools
# --------------

# what a Nat reader's answer says about its input s
def sx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def sx.nat(+s: String) -> sx.NP(s, Wr.get_nat(s)):
  sx.nat.at(s, Wr.get_nat(s), {==})

# what a Bool reader's answer says about its input s
def sx.BP(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def sx.bool.at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> sx.BP(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def sx.bool(+s: String) -> sx.BP(s, Wr.get_bool(s)):
  sx.bool.at(s, Wr.get_bool(s), {==})

# Tags: verify's label, a verdict, an actor
# ----------------------------------------

# what verify's label reader's answer says about its input s
def sx.LbP(s: String, d: Wr.Dec<V.Label>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Wr.put_nat(SSW.w_vlabel(l), r) : String}
    case Wr.Bad{}:
      Unit

def sx.vlabel_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> sx.LbP(s, FS.get_vlabel(Wr.Got{t, s1})):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      pre
    case 3n:
      pre
    case 4n+u:
      Unit{}

# verify's label reader accepts only the tags 0 to 3
def sx.vlabel_tag(-s: String, d: Wr.Dec<Nat>, np: sx.NP(s, d)) -> sx.LbP(s, FS.get_vlabel(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      sx.vlabel_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# what the verdict reader of a slot answers about its input s
def sx.VdP(s: String, d: Wr.Dec<V.Verdict>) -> Type:
  match d:
    case Wr.Got{v, r}:
      {s == Wr.put_nat(SVW.w_verdict(v), r) : String}
    case Wr.Bad{}:
      Unit

def sx.verdict_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> sx.VdP(s, FV.get_verdict(Wr.Got{t, s1})):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      pre
    case 3n:
      pre
    case 4n+u:
      Unit{}

# the verdict reader accepts only the tags 0 to 3
def sx.verdict_tag(-s: String, d: Wr.Dec<Nat>, np: sx.NP(s, d)) -> sx.VdP(s, FV.get_verdict(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      sx.verdict_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# what the actor reader's answer says about its input s
def sx.AcP(s: String, d: Wr.Dec<V.Actor>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_nat(SVW.w_actor(a), r) : String}
    case Wr.Bad{}:
      Unit

def sx.actor_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> sx.AcP(s, FV.get_actor(Wr.Got{t, s1})):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      pre
    case 3n+u:
      Unit{}

# the actor reader accepts only the tags 0 to 2
def sx.actor_tag(-s: String, d: Wr.Dec<Nat>, np: sx.NP(s, d)) -> sx.AcP(s, FV.get_actor(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      sx.actor_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# Gauges: a bar, a mark, a gauge
# ------------------------------

# what the bar reader's answer says about its input s
def sx.BrP(s: String, d: Wr.Dec<St.Bar>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == SSW.w_bar(b, r) : String} & {SSW.fit_bar(b) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.bar_pct(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, np: sx.NP(s1, d)) -> sx.BrP(s, FS.get_bar.pct(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (sx.ext(z => Wr.put_nat(2n, z), s, s1, Wr.put_nat(n, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def sx.bar_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> sx.BrP(s, FS.get_bar(Wr.Got{t, s1})):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      (pre, {==})
    case 2n:
      sx.bar_pct(s, s1, pre, Wr.get_nat(s1), sx.nat(s1))
    case 3n+u:
      Unit{}

# the bar reader accepts only 0, 1, or 2 then a percent that fits
def sx.bar_tag(-s: String, d: Wr.Dec<Nat>, np: sx.NP(s, d)) -> sx.BrP(s, FS.get_bar(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      sx.bar_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# what the mark reader's answer says about its input s
def sx.MkP(s: String, d: Wr.Dec<St.Mark>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == SSW.w_mark(m, r) : String} & {SSW.fit_mark(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.mark_at(-s: String, +c: Nat, +n: Nat, +p: Nat, +s4: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(c, Wr.put_nat(n, Wr.put_nat(p, s4)))) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fp: {LawsBase.wire_fits(p) == True{} : Bool}, d: Wr.Dec<Nat>, np: sx.NP(s4, d)) -> sx.MkP(s, FS.get_mark.at(c, n, p, d)):
  match d:
    case Wr.Got{+at, +r}:
      (e, f) = np
      (sx.ext(z => Wr.put_nat(1n, Wr.put_nat(c, Wr.put_nat(n, Wr.put_nat(p, z)))), s, s4, Wr.put_nat(at, r), pre, e), sx.and_t(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(at))), fc, sx.and_t(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(at)), fn, sx.and_t(LawsBase.wire_fits(p), LawsBase.wire_fits(at), fp, f))))
    case Wr.Bad{}:
      Unit{}

def sx.mark_planned(-s: String, +c: Nat, +n: Nat, +s3: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(c, Wr.put_nat(n, s3))) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, np: sx.NP(s3, d)) -> sx.MkP(s, FS.get_mark.planned(c, n, d)):
  match d:
    case Wr.Got{+p, +s4}:
      (e, f) = np
      sx.mark_at(s, c, n, p, s4, sx.ext(z => Wr.put_nat(1n, Wr.put_nat(c, Wr.put_nat(n, z))), s, s3, Wr.put_nat(p, s4), pre, e), fc, fn, f, Wr.get_nat(s4), sx.nat(s4))
    case Wr.Bad{}:
      Unit{}

def sx.mark_ran(-s: String, +c: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(c, s2)) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Nat>, np: sx.NP(s2, d)) -> sx.MkP(s, FS.get_mark.ran(c, d)):
  match d:
    case Wr.Got{+n, +s3}:
      (e, f) = np
      sx.mark_planned(s, c, n, s3, sx.ext(z => Wr.put_nat(1n, Wr.put_nat(c, z)), s, s2, Wr.put_nat(n, s3), pre, e), fc, f, Wr.get_nat(s3), sx.nat(s3))
    case Wr.Bad{}:
      Unit{}

def sx.mark_caught(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, np: sx.NP(s1, d)) -> sx.MkP(s, FS.get_mark.caught(d)):
  match d:
    case Wr.Got{+c, +s2}:
      (e, f) = np
      sx.mark_ran(s, c, s2, sx.ext(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(c, s2), pre, e), f, Wr.get_nat(s2), sx.nat(s2))
    case Wr.Bad{}:
      Unit{}

def sx.mark_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> sx.MkP(s, FS.get_mark(Wr.Got{t, s1})):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      sx.mark_caught(s, s1, pre, Wr.get_nat(s1), sx.nat(s1))
    case 2n+u:
      Unit{}

# the mark reader accepts only 0, or 1 then four numbers that fit
def sx.mark_tag(-s: String, d: Wr.Dec<Nat>, np: sx.NP(s, d)) -> sx.MkP(s, FS.get_mark(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      sx.mark_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# what the gauge reader's answer says about its input s
def sx.GP(s: String, d: Wr.Dec<St.Gauge>) -> Type:
  match d:
    case Wr.Got{g, r}:
      {s == SSW.w_gauge(g, r) : String} & {SSW.fit_gauge(g) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.gauge_mark(-s: String, +b: St.Bar, +s1: String, pre: {s == SSW.w_bar(b, s1) : String}, fb: {SSW.fit_bar(b) == True{} : Bool}, d: Wr.Dec<St.Mark>, mp: sx.MkP(s1, d)) -> sx.GP(s, FS.get_gauge.mark(b, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e, f) = mp
      (sx.ext(z => SSW.w_bar(b, z), s, s1, SSW.w_mark(m, r), pre, e), sx.and_t(SSW.fit_bar(b), SSW.fit_mark(m), fb, f))
    case Wr.Bad{}:
      Unit{}

def sx.gauge_bar(-s: String, d: Wr.Dec<St.Bar>, bp: sx.BrP(s, d)) -> sx.GP(s, FS.get_gauge.bar(d)):
  match d:
    case Wr.Got{+b, +s1}:
      (e, f) = bp
      sx.gauge_mark(s, b, s1, e, f, FS.get_mark(Wr.get_nat(s1)), sx.mark_tag(s1, Wr.get_nat(s1), sx.nat(s1)))
    case Wr.Bad{}:
      Unit{}

# the gauge reader accepts only a bar, then a mark
def sx.gauge(+s: String) -> sx.GP(s, FS.get_gauge(s)):
  sx.gauge_bar(s, FS.get_bar(Wr.get_nat(s)), sx.bar_tag(s, Wr.get_nat(s), sx.nat(s)))

# Slots
# -----

# what the slot reader's answer says about its input s
def sx.SlP(s: String, d: Wr.Dec<V.Slot>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == SVW.w_slot(x, r) : String} & {SVW.fit_slot(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.slot_at(-s: String, +v: V.Verdict, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(SVW.w_verdict(v), s2)) : String}, d: Wr.Dec<Nat>, np: sx.NP(s2, d)) -> sx.SlP(s, FV.get_slot.at(v, d)):
  match d:
    case Wr.Got{+at, +r}:
      (e, f) = np
      (sx.ext(z => Wr.put_nat(1n, Wr.put_nat(SVW.w_verdict(v), z)), s, s2, Wr.put_nat(at, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def sx.slot_verdict(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<V.Verdict>, vp: sx.VdP(s1, d)) -> sx.SlP(s, FV.get_slot.verdict(d)):
  match d:
    case Wr.Got{+v, +s2}:
      sx.slot_at(s, v, s2, sx.ext(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(SVW.w_verdict(v), s2), pre, vp), Wr.get_nat(s2), sx.nat(s2))
    case Wr.Bad{}:
      Unit{}

def sx.slot_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> sx.SlP(s, FV.get_slot.tag(Wr.Got{t, s1})):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      sx.slot_verdict(s, s1, pre, FV.get_verdict(Wr.get_nat(s1)), sx.verdict_tag(s1, Wr.get_nat(s1), sx.nat(s1)))
    case 2n+u:
      Unit{}

def sx.slot_tag(-s: String, d: Wr.Dec<Nat>, np: sx.NP(s, d)) -> sx.SlP(s, FV.get_slot.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      sx.slot_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# the slot reader accepts only 0, or 1 then a verdict and a state that fits
def sx.slot(+s: String) -> sx.SlP(s, FV.get_slot(s)):
  sx.slot_tag(s, Wr.get_nat(s), sx.nat(s))

# Lists: gauges, slots
# --------------------

# what the item reader's answer says about its input s (k items)
def sx.GIP(s: String, k: Nat, d: Wr.Dec<List<&2, St.Gauge>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LSE.se.items(xs, r) : String} & ({List.length(&2, St.Gauge, xs) == k : Nat} & {SSW.fit_gauges.items(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def sx.gauge_at(+s: String, -d: Wr.Dec<St.Gauge>, ed: {FS.get_gauge(s) == d : Wr.Dec<St.Gauge>}) -> sx.GP(s, d):
  %ed : sx.GP(s, _)
  sx.gauge(s)

# an item before items read
def sx.gauge_cons(-s: String, +c: St.Gauge, +r1: String, -k: Nat, d: Wr.Dec<List<&2, St.Gauge>>, ih: sx.GIP(r1, k, d), cp: sx.GP(s, Wr.Got{c, r1})) -> sx.GIP(s, 1n+k, LawsBase.wire_items.cons(St.Gauge, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ih
      (ec, fc) = cp
      (sx.ext(z => SSW.w_gauge(c, z), s, r1, LSE.se.items(xs, r), ec, e1), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, St.Gauge, xs), k, e2), sx.and_t(SSW.fit_gauge(c), SSW.fit_gauges.items(xs), fc, e3)))
    case Wr.Bad{}:
      Unit{}

# mm + 1 items, the first read from s as cur
def sx.gauge_items(mm: Nat, cur: Wr.Dec<St.Gauge>, +s: String, er: {FS.get_gauge(s) == cur : Wr.Dec<St.Gauge>}) -> sx.GIP(s, 1n+mm, LawsBase.wire_items.then(St.Gauge, cur, r => LawsBase.wire_items(~St.Gauge, ~FS.get_gauge, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      sx.gauge_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), sx.gauge_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      sx.gauge_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(St.Gauge, FS.get_gauge(r1), r => LawsBase.wire_items(~St.Gauge, ~FS.get_gauge, k, r)), sx.gauge_items(k, FS.get_gauge(r1), r1, {==}), sx.gauge_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def sx.gauge_items_of(k: Nat, +s: String) -> sx.GIP(s, k, LawsBase.wire_items(~St.Gauge, ~FS.get_gauge, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      sx.gauge_items(mm, FS.get_gauge(s), s, {==})

# what the list reader's answer says about its input s
def sx.GLP(s: String, d: Wr.Dec<List<&2, St.Gauge>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == SSW.w_gauges(xs, r) : String} & {SSW.fit_gauges(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.gauge_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, St.Gauge>>, ip: sx.GIP(s1, k, d)) -> sx.GLP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +n = List.length(&2, St.Gauge, xs)
      +w = LSE.se.items(xs, r)
      +es = sx.ext(z => Wr.put_nat(k, z), s, s1, w, en, e1)
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +ew = Equal.sym(String, SSW.w_gauges(xs, r), Wr.put_nat(n, w), LSE.se.w_gauges(xs, r))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(n, w), SSW.w_gauges(xs, r), Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ew), sx.and_t(LawsBase.wire_fits(n), SSW.fit_gauges.items(xs), fl, e3))
    case Wr.Bad{}:
      Unit{}

def sx.gauge_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.GLP(s, LawsBase.wire_read_list.count(~St.Gauge, ~FS.get_gauge, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      sx.gauge_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~St.Gauge, ~FS.get_gauge, k, s1), sx.gauge_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

# the list reader accepts only a spelled list that fits
def sx.gauges(+s: String) -> sx.GLP(s, Wr.get_list(~St.Gauge, ~FS.get_gauge, s)):
  %Equal.sym(Wr.Dec<List<&2, St.Gauge>>, Wr.get_list(~St.Gauge, ~FS.get_gauge, s), LawsBase.wire_read_list(~St.Gauge, ~FS.get_gauge, s), Wire.wire_list_reads_items(~St.Gauge, ~FS.get_gauge, s)) : sx.GLP(s, _)
  sx.gauge_count(s, Wr.get_nat(s), {==})

# what the item reader's answer says about its input s (k items)
def sx.SIP(s: String, k: Nat, d: Wr.Dec<List<&2, V.Slot>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LVE.ve.items(xs, r) : String} & ({List.length(&2, V.Slot, xs) == k : Nat} & {SVW.fit_slots.items(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def sx.slot_at_s(+s: String, -d: Wr.Dec<V.Slot>, ed: {FV.get_slot(s) == d : Wr.Dec<V.Slot>}) -> sx.SlP(s, d):
  %ed : sx.SlP(s, _)
  sx.slot(s)

# an item before items read
def sx.slot_cons(-s: String, +c: V.Slot, +r1: String, -k: Nat, d: Wr.Dec<List<&2, V.Slot>>, ih: sx.SIP(r1, k, d), cp: sx.SlP(s, Wr.Got{c, r1})) -> sx.SIP(s, 1n+k, LawsBase.wire_items.cons(V.Slot, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ih
      (ec, fc) = cp
      (sx.ext(z => SVW.w_slot(c, z), s, r1, LVE.ve.items(xs, r), ec, e1), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, V.Slot, xs), k, e2), sx.and_t(SVW.fit_slot(c), SVW.fit_slots.items(xs), fc, e3)))
    case Wr.Bad{}:
      Unit{}

# mm + 1 items, the first read from s as cur
def sx.slot_items(mm: Nat, cur: Wr.Dec<V.Slot>, +s: String, er: {FV.get_slot(s) == cur : Wr.Dec<V.Slot>}) -> sx.SIP(s, 1n+mm, LawsBase.wire_items.then(V.Slot, cur, r => LawsBase.wire_items(~V.Slot, ~FV.get_slot, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      sx.slot_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), sx.slot_at_s(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      sx.slot_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(V.Slot, FV.get_slot(r1), r => LawsBase.wire_items(~V.Slot, ~FV.get_slot, k, r)), sx.slot_items(k, FV.get_slot(r1), r1, {==}), sx.slot_at_s(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def sx.slot_items_of(k: Nat, +s: String) -> sx.SIP(s, k, LawsBase.wire_items(~V.Slot, ~FV.get_slot, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      sx.slot_items(mm, FV.get_slot(s), s, {==})

# what the list reader's answer says about its input s
def sx.SLP(s: String, d: Wr.Dec<List<&2, V.Slot>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == SVW.w_slots(xs, r) : String} & {SVW.fit_slots(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.slot_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, V.Slot>>, ip: sx.SIP(s1, k, d)) -> sx.SLP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +n = List.length(&2, V.Slot, xs)
      +w = LVE.ve.items(xs, r)
      +es = sx.ext(z => Wr.put_nat(k, z), s, s1, w, en, e1)
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +ew = Equal.sym(String, SVW.w_slots(xs, r), Wr.put_nat(n, w), LVE.ve.w_slots(xs, r))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(n, w), SVW.w_slots(xs, r), Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ew), sx.and_t(LawsBase.wire_fits(n), SVW.fit_slots.items(xs), fl, e3))
    case Wr.Bad{}:
      Unit{}

def sx.slot_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.SLP(s, LawsBase.wire_read_list.count(~V.Slot, ~FV.get_slot, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      sx.slot_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~V.Slot, ~FV.get_slot, k, s1), sx.slot_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

# the list reader accepts only a spelled list that fits
def sx.slots(+s: String) -> sx.SLP(s, Wr.get_list(~V.Slot, ~FV.get_slot, s)):
  %Equal.sym(Wr.Dec<List<&2, V.Slot>>, Wr.get_list(~V.Slot, ~FV.get_slot, s), LawsBase.wire_read_list(~V.Slot, ~FV.get_slot, s), Wire.wire_list_reads_items(~V.Slot, ~FV.get_slot, s)) : sx.SLP(s, _)
  sx.slot_count(s, Wr.get_nat(s), {==})

# Requests
# --------

# what the request reader's answer says about its input s
def sx.QP(s: String, d: Wr.Dec<FS.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == SSW.w_req(q, r) : String} & {SSW.fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# 0: settle
def sx.st_gs(-s: String, +l: V.Label, +now: Nat, +s3: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(SSW.w_vlabel(l), Wr.put_nat(now, s3))) : String}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<List<&2, St.Gauge>>, gp: sx.GLP(s3, d)) -> sx.QP(s, FS.get_req.settle_gs(l, now, d)):
  match d:
    case Wr.Got{+gs, +r}:
      (e, f) = gp
      (sx.ext(z => Wr.put_nat(0n, Wr.put_nat(SSW.w_vlabel(l), Wr.put_nat(now, z))), s, s3, SSW.w_gauges(gs, r), pre, e), sx.and_t(LawsBase.wire_fits(now), SSW.fit_gauges(gs), fnow, f))
    case Wr.Bad{}:
      Unit{}

def sx.st_now(-s: String, +l: V.Label, +s2: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(SSW.w_vlabel(l), s2)) : String}, d: Wr.Dec<Nat>, np: sx.NP(s2, d)) -> sx.QP(s, FS.get_req.settle_now(l, d)):
  match d:
    case Wr.Got{+now, +s3}:
      (e, f) = np
      sx.st_gs(s, l, now, s3, sx.ext(z => Wr.put_nat(0n, Wr.put_nat(SSW.w_vlabel(l), z)), s, s2, Wr.put_nat(now, s3), pre, e), f, FS.get_gauges(s3), sx.gauges(s3))
    case Wr.Bad{}:
      Unit{}

def sx.st_l(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<V.Label>, lp: sx.LbP(s1, d)) -> sx.QP(s, FS.get_req.settle(d)):
  match d:
    case Wr.Got{+l, +s2}:
      sx.st_now(s, l, s2, sx.ext(z => Wr.put_nat(0n, z), s, s1, Wr.put_nat(SSW.w_vlabel(l), s2), pre, lp), Wr.get_nat(s2), sx.nat(s2))
    case Wr.Bad{}:
      Unit{}

# 1: label
def sx.lb_gs(-s: String, +l: V.Label, +now: Nat, +s3: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), Wr.put_nat(now, s3))) : String}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<List<&2, St.Gauge>>, gp: sx.GLP(s3, d)) -> sx.QP(s, FS.get_req.label_gs(l, now, d)):
  match d:
    case Wr.Got{+gs, +r}:
      (e, f) = gp
      (sx.ext(z => Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), Wr.put_nat(now, z))), s, s3, SSW.w_gauges(gs, r), pre, e), sx.and_t(LawsBase.wire_fits(now), SSW.fit_gauges(gs), fnow, f))
    case Wr.Bad{}:
      Unit{}

def sx.lb_now(-s: String, +l: V.Label, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), s2)) : String}, d: Wr.Dec<Nat>, np: sx.NP(s2, d)) -> sx.QP(s, FS.get_req.label_now(l, d)):
  match d:
    case Wr.Got{+now, +s3}:
      (e, f) = np
      sx.lb_gs(s, l, now, s3, sx.ext(z => Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), z)), s, s2, Wr.put_nat(now, s3), pre, e), f, FS.get_gauges(s3), sx.gauges(s3))
    case Wr.Bad{}:
      Unit{}

def sx.lb_l(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<V.Label>, lp: sx.LbP(s1, d)) -> sx.QP(s, FS.get_req.label(d)):
  match d:
    case Wr.Got{+l, +s2}:
      sx.lb_now(s, l, s2, sx.ext(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(SSW.w_vlabel(l), s2), pre, lp), Wr.get_nat(s2), sx.nat(s2))
    case Wr.Bad{}:
      Unit{}

# 2: the exit code
def sx.ex_gs(-s: String, +base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +s4: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, SVW.w_slots(slots, s4)))) : String}, fb: {LawsBase.wire_fits(base) == True{} : Bool}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fsl: {SVW.fit_slots(slots) == True{} : Bool}, d: Wr.Dec<List<&2, St.Gauge>>, gp: sx.GLP(s4, d)) -> sx.QP(s, FS.get_req.exit_gs(base, now, slots, d)):
  match d:
    case Wr.Got{+gs, +r}:
      (e, f) = gp
      +fs = sx.and_t(SVW.fit_slots(slots), SSW.fit_gauges(gs), fsl, f)
      +fn = sx.and_t(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), SSW.fit_gauges(gs)), fnow, fs)
      (sx.ext(z => Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, SVW.w_slots(slots, z)))), s, s4, SSW.w_gauges(gs, r), pre, e), sx.and_t(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), SSW.fit_gauges(gs))), fb, fn))
    case Wr.Bad{}:
      Unit{}

def sx.ex_slots(-s: String, +base: Nat, +now: Nat, +s3: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, s3))) : String}, fb: {LawsBase.wire_fits(base) == True{} : Bool}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<List<&2, V.Slot>>, sp: sx.SLP(s3, d)) -> sx.QP(s, FS.get_req.exit_slots(base, now, d)):
  match d:
    case Wr.Got{+slots, +s4}:
      (e, f) = sp
      sx.ex_gs(s, base, now, slots, s4, sx.ext(z => Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, z))), s, s3, SVW.w_slots(slots, s4), pre, e), fb, fnow, f, FS.get_gauges(s4), sx.gauges(s4))
    case Wr.Bad{}:
      Unit{}

def sx.ex_now(-s: String, +base: Nat, +s2: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(base, s2)) : String}, fb: {LawsBase.wire_fits(base) == True{} : Bool}, d: Wr.Dec<Nat>, np: sx.NP(s2, d)) -> sx.QP(s, FS.get_req.exit_now(base, d)):
  match d:
    case Wr.Got{+now, +s3}:
      (e, f) = np
      sx.ex_slots(s, base, now, s3, sx.ext(z => Wr.put_nat(2n, Wr.put_nat(base, z)), s, s2, Wr.put_nat(now, s3), pre, e), fb, f, FV.get_slots(s3), sx.slots(s3))
    case Wr.Bad{}:
      Unit{}

def sx.ex_base(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, np: sx.NP(s1, d)) -> sx.QP(s, FS.get_req.exit(d)):
  match d:
    case Wr.Got{+base, +s2}:
      (e, f) = np
      sx.ex_now(s, base, s2, sx.ext(z => Wr.put_nat(2n, z), s, s1, Wr.put_nat(base, s2), pre, e), f, Wr.get_nat(s2), sx.nat(s2))
    case Wr.Bad{}:
      Unit{}

# 3: a record
def sx.rc_gs(-s: String, +who: V.Actor, +i: Nat, +m: St.Mark, +s4: String, pre: {s == Wr.put_nat(3n, Wr.put_nat(SVW.w_actor(who), Wr.put_nat(i, SSW.w_mark(m, s4)))) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, fm: {SSW.fit_mark(m) == True{} : Bool}, d: Wr.Dec<List<&2, St.Gauge>>, gp: sx.GLP(s4, d)) -> sx.QP(s, FS.get_req.record_gs(who, i, m, d)):
  match d:
    case Wr.Got{+gs, +r}:
      (e, f) = gp
      (sx.ext(z => Wr.put_nat(3n, Wr.put_nat(SVW.w_actor(who), Wr.put_nat(i, SSW.w_mark(m, z)))), s, s4, SSW.w_gauges(gs, r), pre, e), sx.and_t(LawsBase.wire_fits(i), Bool.and(SSW.fit_mark(m), SSW.fit_gauges(gs)), fi, sx.and_t(SSW.fit_mark(m), SSW.fit_gauges(gs), fm, f)))
    case Wr.Bad{}:
      Unit{}

def sx.rc_mark(-s: String, +who: V.Actor, +i: Nat, +s3: String, pre: {s == Wr.put_nat(3n, Wr.put_nat(SVW.w_actor(who), Wr.put_nat(i, s3))) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<St.Mark>, mp: sx.MkP(s3, d)) -> sx.QP(s, FS.get_req.record_mark(who, i, d)):
  match d:
    case Wr.Got{+m, +s4}:
      (e, f) = mp
      sx.rc_gs(s, who, i, m, s4, sx.ext(z => Wr.put_nat(3n, Wr.put_nat(SVW.w_actor(who), Wr.put_nat(i, z))), s, s3, SSW.w_mark(m, s4), pre, e), fi, f, FS.get_gauges(s4), sx.gauges(s4))
    case Wr.Bad{}:
      Unit{}

def sx.rc_i(-s: String, +who: V.Actor, +s2: String, pre: {s == Wr.put_nat(3n, Wr.put_nat(SVW.w_actor(who), s2)) : String}, d: Wr.Dec<Nat>, np: sx.NP(s2, d)) -> sx.QP(s, FS.get_req.record_i(who, d)):
  match d:
    case Wr.Got{+i, +s3}:
      (e, f) = np
      sx.rc_mark(s, who, i, s3, sx.ext(z => Wr.put_nat(3n, Wr.put_nat(SVW.w_actor(who), z)), s, s2, Wr.put_nat(i, s3), pre, e), f, FS.get_mark(Wr.get_nat(s3)), sx.mark_tag(s3, Wr.get_nat(s3), sx.nat(s3)))
    case Wr.Bad{}:
      Unit{}

def sx.rc_who(-s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<V.Actor>, ap: sx.AcP(s1, d)) -> sx.QP(s, FS.get_req.record(d)):
  match d:
    case Wr.Got{+who, +s2}:
      sx.rc_i(s, who, s2, sx.ext(z => Wr.put_nat(3n, z), s, s1, Wr.put_nat(SVW.w_actor(who), s2), pre, ap), Wr.get_nat(s2), sx.nat(s2))
    case Wr.Bad{}:
      Unit{}

# 4: the strength of one check
def sx.sg_g(-s: String, +now: Nat, +s2: String, pre: {s == Wr.put_nat(4n, Wr.put_nat(now, s2)) : String}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<St.Gauge>, gp: sx.GP(s2, d)) -> sx.QP(s, FS.get_req.strength_g(now, d)):
  match d:
    case Wr.Got{+g, +r}:
      (e, f) = gp
      (sx.ext(z => Wr.put_nat(4n, Wr.put_nat(now, z)), s, s2, SSW.w_gauge(g, r), pre, e), sx.and_t(LawsBase.wire_fits(now), SSW.fit_gauge(g), fnow, f))
    case Wr.Bad{}:
      Unit{}

def sx.sg_now(-s: String, +s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<Nat>, np: sx.NP(s1, d)) -> sx.QP(s, FS.get_req.strength(d)):
  match d:
    case Wr.Got{+now, +s2}:
      (e, f) = np
      sx.sg_g(s, now, s2, sx.ext(z => Wr.put_nat(4n, z), s, s1, Wr.put_nat(now, s2), pre, e), f, FS.get_gauge(s2), sx.gauge(s2))
    case Wr.Bad{}:
      Unit{}

def sx.req_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> sx.QP(s, FS.get_req(Wr.Got{t, s1})):
  match t:
    case 0n:
      sx.st_l(s, s1, pre, FS.get_vlabel(Wr.get_nat(s1)), sx.vlabel_tag(s1, Wr.get_nat(s1), sx.nat(s1)))
    case 1n:
      sx.lb_l(s, s1, pre, FS.get_vlabel(Wr.get_nat(s1)), sx.vlabel_tag(s1, Wr.get_nat(s1), sx.nat(s1)))
    case 2n:
      sx.ex_base(s, s1, pre, Wr.get_nat(s1), sx.nat(s1))
    case 3n:
      sx.rc_who(s, s1, pre, FV.get_actor(Wr.get_nat(s1)), sx.actor_tag(s1, Wr.get_nat(s1), sx.nat(s1)))
    case 4n:
      sx.sg_now(s, s1, pre, Wr.get_nat(s1), sx.nat(s1))
    case 5n+u:
      Unit{}

def sx.req_tag(-s: String, d: Wr.Dec<Nat>, np: sx.NP(s, d)) -> sx.QP(s, FS.get_req(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      sx.req_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# the request reader accepts only a spelled request that fits, before the
# rest of the input
def sx.req(+s: String) -> sx.QP(s, FS.get_req(Wr.get_nat(s))):
  sx.req_tag(s, Wr.get_nat(s), sx.nat(s))

# The answer
# ----------

def sx.step_ok(x: St.Step) -> {LawsBase.wire_opens_err(SSW.w_step(x)) == False{} : Bool}:
  match x:
    case St.Measure{i}:
      Wire.wire_nat_not_err(0n, Wr.put_nat(i, ""))
    case St.End{l}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(SSW.w_label(l), ""))

def sx.recorded_ok(r: Bool & List<&2, St.Gauge>) -> {LawsBase.wire_opens_err(SSW.w_recorded(r)) == False{} : Bool}:
  (+ok, +gs) = r
  Wire.wire_bool_not_err(ok, SSW.w_gauges(gs, ""))

def sx.reply_ok(q: FS.Req) -> {LawsBase.wire_opens_err(SSW.w_reply(q)) == False{} : Bool}:
  match q:
    case FS.QSettle{l, now, gs}:
      sx.step_ok(St.settle(l, now, gs))
    case FS.QLabel{l, now, gs}:
      Wire.wire_nat_not_err(SSW.w_label(St.label(l, now, gs)), "")
    case FS.QExit{base, now, slots, gs}:
      Wire.wire_nat_not_err(St.exit(base, now, slots, gs), "")
    case FS.QRecord{who, i, m, gs}:
      sx.recorded_ok(St.record(who, i, m, gs))
    case FS.QStrength{now, g}:
      Wire.wire_nat_not_err(SSW.w_strength(St.strength(now, g)), "")

# the entry's answer to a request never opens with 'E'
def sx.answer_ok(+q: FS.Req) -> {LawsBase.wire_opens_err(FS.answer(q)) == False{} : Bool}:
  %Equal.sym(String, FS.answer(q), SSW.w_reply(q), LSE.se.answer(q)) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  sx.reply_ok(q)
