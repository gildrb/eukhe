# eukhe: the laws of area effort, section entry: the entry bend/ffi_effort.bend on every input, from a
# reader, the decisions and a speller of its own, and the session (S10), pinned

import Base
import ../../bend/effort.bend as Ef
import ../../bend/ffi_effort.bend as FEf
import ../../bend/wire.bend as Wr

# The entry, independently of bend/ffi_effort.bend and of the model's
# functions: a reader of the request grammar (the header of
# bend/ffi_effort.bend) built from the wire primitives, the ladder, the
# clamp and the cycle as bend/effort.bend's header and the S6.9 laws above
# state them, and a speller of the reply from the wire primitives.

# Reader
# ------

# a level: its tag, off 0 .. max 6
def er.lv.tag(t: Nat, s: String) -> Wr.Dec<Ef.Lv>:
  match t:
    case 0n:
      Wr.Got{Ef.Off{}, s}
    case 1n:
      Wr.Got{Ef.Minimal{}, s}
    case 2n:
      Wr.Got{Ef.Low{}, s}
    case 3n:
      Wr.Got{Ef.Medium{}, s}
    case 4n:
      Wr.Got{Ef.High{}, s}
    case 5n:
      Wr.Got{Ef.Xhigh{}, s}
    case 6n:
      Wr.Got{Ef.Max{}, s}
    case 7n+p:
      Wr.Bad{}

def er.lv.go(r: Wr.Dec<Nat>) -> Wr.Dec<Ef.Lv>:
  match r:
    case Wr.Got{t, s}:
      er.lv.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def er.lv(s: String) -> Wr.Dec<Ef.Lv>:
  er.lv.go(Wr.get_nat(s))

# an entry of a map: missing 0, null 1, a wire string 2
def er.ent.tag(t: Nat, s: String) -> Wr.Dec<Ef.Ent>:
  match t:
    case 0n:
      Wr.Got{Ef.Missing{}, s}
    case 1n:
      Wr.Got{Ef.Null{}, s}
    case 2n:
      Wr.Got{Ef.Wire{}, s}
    case 3n+p:
      Wr.Bad{}

def er.ent(r: Wr.Dec<Nat>) -> Wr.Dec<Ef.Ent>:
  match r:
    case Wr.Got{t, s}:
      er.ent.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a map: the entries of off .. max
def er.map.mx(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, r: Wr.Dec<Ef.Ent>) -> Wr.Dec<Ef.LvMap>:
  match r:
    case Wr.Got{mx, s}:
      Wr.Got{Ef.LvMap{o, mi, lo, me, hi, xh, mx}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def er.map.xh(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, r: Wr.Dec<Ef.Ent>) -> Wr.Dec<Ef.LvMap>:
  match r:
    case Wr.Got{xh, s}:
      er.map.mx(o, mi, lo, me, hi, xh, er.ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def er.map.hi(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, r: Wr.Dec<Ef.Ent>) -> Wr.Dec<Ef.LvMap>:
  match r:
    case Wr.Got{hi, s}:
      er.map.xh(o, mi, lo, me, hi, er.ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def er.map.me(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, r: Wr.Dec<Ef.Ent>) -> Wr.Dec<Ef.LvMap>:
  match r:
    case Wr.Got{me, s}:
      er.map.hi(o, mi, lo, me, er.ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def er.map.lo(o: Ef.Ent, mi: Ef.Ent, r: Wr.Dec<Ef.Ent>) -> Wr.Dec<Ef.LvMap>:
  match r:
    case Wr.Got{lo, s}:
      er.map.me(o, mi, lo, er.ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def er.map.mi(o: Ef.Ent, r: Wr.Dec<Ef.Ent>) -> Wr.Dec<Ef.LvMap>:
  match r:
    case Wr.Got{mi, s}:
      er.map.lo(o, mi, er.ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def er.map.o(r: Wr.Dec<Ef.Ent>) -> Wr.Dec<Ef.LvMap>:
  match r:
    case Wr.Got{o, s}:
      er.map.mi(o, er.ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def er.map(s: String) -> Wr.Dec<Ef.LvMap>:
  er.map.o(er.ent(Wr.get_nat(s)))

# a Maybe<LvMap>: 0 none | 1, then the map
def er.mmap.some(r: Wr.Dec<Ef.LvMap>) -> Wr.Dec<Maybe<&2, Ef.LvMap>>:
  match r:
    case Wr.Got{m, s}:
      Wr.Got{Some{m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def er.mmap.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Ef.LvMap>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      er.mmap.some(er.map(s))
    case 2n+p:
      Wr.Bad{}

def er.mmap(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Ef.LvMap>>:
  match r:
    case Wr.Got{t, s}:
      er.mmap.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a direction: forward 0, backward 1
def er.dir.tag(t: Nat, s: String) -> Wr.Dec<Ef.Dir>:
  match t:
    case 0n:
      Wr.Got{Ef.Forward{}, s}
    case 1n:
      Wr.Got{Ef.Backward{}, s}
    case 2n+p:
      Wr.Bad{}

def er.dir(r: Wr.Dec<Nat>) -> Wr.Dec<Ef.Dir>:
  match r:
    case Wr.Got{t, s}:
      er.dir.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a list of levels
def er.lvs(s: String) -> Wr.Dec<List<&2, Ef.Lv>>:
  Wr.get_list(~Ef.Lv, ~er.lv, s)

# the facts: flag, by_map, the explicit map, the rule's map, the reasoning
# and the plain default ladders
def er.facts.pl(f: Bool, bm: Bool, ex: Maybe<&2, Ef.LvMap>, ru: Maybe<&2, Ef.LvMap>, re: List<&2, Ef.Lv>, r: Wr.Dec<List<&2, Ef.Lv>>) -> Wr.Dec<FEf.Facts>:
  match r:
    case Wr.Got{pl, s}:
      Wr.Got{FEf.Facts{f, bm, ex, ru, re, pl}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def er.facts.re(f: Bool, bm: Bool, ex: Maybe<&2, Ef.LvMap>, ru: Maybe<&2, Ef.LvMap>, r: Wr.Dec<List<&2, Ef.Lv>>) -> Wr.Dec<FEf.Facts>:
  match r:
    case Wr.Got{re, s}:
      er.facts.pl(f, bm, ex, ru, re, er.lvs(s))
    case Wr.Bad{}:
      Wr.Bad{}

def er.facts.ru(f: Bool, bm: Bool, ex: Maybe<&2, Ef.LvMap>, r: Wr.Dec<Maybe<&2, Ef.LvMap>>) -> Wr.Dec<FEf.Facts>:
  match r:
    case Wr.Got{ru, s}:
      er.facts.re(f, bm, ex, ru, er.lvs(s))
    case Wr.Bad{}:
      Wr.Bad{}

def er.facts.ex(f: Bool, bm: Bool, r: Wr.Dec<Maybe<&2, Ef.LvMap>>) -> Wr.Dec<FEf.Facts>:
  match r:
    case Wr.Got{ex, s}:
      er.facts.ru(f, bm, ex, er.mmap(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def er.facts.bm(f: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<FEf.Facts>:
  match r:
    case Wr.Got{bm, s}:
      er.facts.ex(f, bm, er.mmap(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def er.facts.f(r: Wr.Dec<Bool>) -> Wr.Dec<FEf.Facts>:
  match r:
    case Wr.Got{f, s}:
      er.facts.bm(f, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def er.facts(s: String) -> Wr.Dec<FEf.Facts>:
  er.facts.f(Wr.get_bool(s))

# 0 the offer: the facts
def er.offered(r: Wr.Dec<FEf.Facts>) -> Wr.Dec<FEf.Req>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{FEf.Offered{f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# 1 the clamp: the facts, the level
def er.clamp.l(f: FEf.Facts, r: Wr.Dec<Ef.Lv>) -> Wr.Dec<FEf.Req>:
  match r:
    case Wr.Got{l, s}:
      Wr.Got{FEf.Clamp{f, l}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def er.clamp(r: Wr.Dec<FEf.Facts>) -> Wr.Dec<FEf.Req>:
  match r:
    case Wr.Got{f, s}:
      er.clamp.l(f, er.lv(s))
    case Wr.Bad{}:
      Wr.Bad{}

# 2 the cycle: the facts, the level, the direction
def er.cycle.d(f: FEf.Facts, l: Ef.Lv, r: Wr.Dec<Ef.Dir>) -> Wr.Dec<FEf.Req>:
  match r:
    case Wr.Got{d, s}:
      Wr.Got{FEf.Cycle{f, l, d}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def er.cycle.l(f: FEf.Facts, r: Wr.Dec<Ef.Lv>) -> Wr.Dec<FEf.Req>:
  match r:
    case Wr.Got{l, s}:
      er.cycle.d(f, l, er.dir(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def er.cycle(r: Wr.Dec<FEf.Facts>) -> Wr.Dec<FEf.Req>:
  match r:
    case Wr.Got{f, s}:
      er.cycle.l(f, er.lv(s))
    case Wr.Bad{}:
      Wr.Bad{}

def er.req.tag(t: Nat, s: String) -> Wr.Dec<FEf.Req>:
  match t:
    case 0n:
      er.offered(er.facts(s))
    case 1n:
      er.clamp(er.facts(s))
    case 2n:
      er.cycle(er.facts(s))
    case 3n+p:
      Wr.Bad{}

def er.req(r: Wr.Dec<Nat>) -> Wr.Dec<FEf.Req>:
  match r:
    case Wr.Got{t, s}:
      er.req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def er.read(s: String) -> Wr.Dec<FEf.Req>:
  er.req(Wr.get_nat(s))

# Decisions
# ---------

# b ? t : e
def es.if(-A: Data, b: Bool, t: A, e: A) -> A:
  match b:
    case True{}:
      t
    case False{}:
      e

# a level's place on the ladder off, minimal, low, medium, high, xhigh, max
def es.idx(l: Ef.Lv) -> Nat:
  match l:
    case Ef.Off{}:
      0n
    case Ef.Minimal{}:
      1n
    case Ef.Low{}:
      2n
    case Ef.Medium{}:
      3n
    case Ef.High{}:
      4n
    case Ef.Xhigh{}:
      5n
    case Ef.Max{}:
      6n

def es.same(a: Ef.Lv, b: Ef.Lv) -> Bool:
  Nat.is_eq(es.idx(a), es.idx(b))

# xs lists the level l
def es.has(xs: List<&2, Ef.Lv>, +l: Ef.Lv) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(es.same(x, l), es.has(rest, l))

def es.ladder() -> List<&2, Ef.Lv>:
  [Ef.Off{}, Ef.Minimal{}, Ef.Low{}, Ef.Medium{}, Ef.High{}, Ef.Xhigh{}, Ef.Max{}]

# the entry of the level l in the map m
def es.entry(l: Ef.Lv, m: Ef.LvMap) -> Ef.Ent:
  match l:
    case Ef.Off{}:
      match m:
        case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
          o
    case Ef.Minimal{}:
      match m:
        case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
          mi
    case Ef.Low{}:
      match m:
        case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
          lo
    case Ef.Medium{}:
      match m:
        case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
          me
    case Ef.High{}:
      match m:
        case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
          hi
    case Ef.Xhigh{}:
      match m:
        case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
          xh
    case Ef.Max{}:
      match m:
        case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
          mx

def es.wire(e: Ef.Ent) -> Bool:
  match e:
    case Ef.Missing{}:
      False{}
    case Ef.Null{}:
      False{}
    case Ef.Wire{}:
      True{}

# an explicit map gives some level a wire string
def es.wired(explicit: Maybe<&2, Ef.LvMap>) -> Bool:
  match explicit:
    case None{}:
      False{}
    case Some{m}:
      match m:
        case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
          Bool.or(es.wire(o), Bool.or(es.wire(mi), Bool.or(es.wire(lo), Bool.or(es.wire(me), Bool.or(es.wire(hi), Bool.or(es.wire(xh), es.wire(mx)))))))

# a model reasons by its flag, or, a registry model (by_map), by an
# explicit map that gives some level a wire string (laws/infer.bend
# quirk_ladder_flag_reasons, quirk_ladder_map_reasons,
# quirk_ladder_reasons_only_so)
def es.reasons(flag: Bool, bm: Bool, explicit: Maybe<&2, Ef.LvMap>) -> Bool:
  Bool.or(flag, Bool.and(bm, es.wired(explicit)))

# the chosen ladder: the explicit map, else the rule's, else no entry
# (laws/infer.bend quirk_ladder_explicit_decides, quirk_ladder_rule_decides,
# quirk_ladder_default_decides)
def es.chosen(explicit: Maybe<&2, Ef.LvMap>, rule: Maybe<&2, Ef.LvMap>) -> Ef.LvMap:
  match explicit:
    case Some{e}:
      e
    case None{}:
      match rule:
        case Some{r}:
          r
        case None{}:
          Ef.LvMap{Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}, Ef.Missing{}}

# a reasoning model's level with chosen entry e: a wire string offers it,
# null does not, no entry offers it when the reasoning default ladder lists
# it (quirk_ladder_offered_exact)
def es.keep.e(e: Ef.Ent, rs: List<&2, Ef.Lv>, +l: Ef.Lv) -> Bool:
  match e:
    case Ef.Missing{}:
      es.has(rs, l)
    case Ef.Null{}:
      False{}
    case Ef.Wire{}:
      True{}

# whether the level l is offered: by the chosen ladder for a reasoning
# model, by the plain default ladder for another (quirk_ladder_plain_exact)
def es.keep(r: Bool, ch: Ef.LvMap, rs: List<&2, Ef.Lv>, pl: List<&2, Ef.Lv>, +l: Ef.Lv) -> Bool:
  match r:
    case True{}:
      es.keep.e(es.entry(l, ch), rs, l)
    case False{}:
      es.has(pl, l)

# the levels of xs that are offered, in order
def es.offer(xs: List<&2, Ef.Lv>, +r: Bool, +ch: Ef.LvMap, +rs: List<&2, Ef.Lv>, +pl: List<&2, Ef.Lv>) -> List<&2, Ef.Lv>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +rest:
      es.if(List<&2, Ef.Lv>, es.keep(r, ch, rs, pl, x), x <> es.offer(rest, r, ch, rs, pl), es.offer(rest, r, ch, rs, pl))

# the levels a model offers, in ladder order
def es.offered(f: FEf.Facts) -> List<&2, Ef.Lv>:
  match f:
    case FEf.Facts{flag, bm, +ex, ru, rs, pl}:
      es.offer(es.ladder(), es.reasons(flag, bm, ex), es.chosen(ex, ru), rs, pl)

# the first level of xs that lad lists
def es.pick(+lad: List<&2, Ef.Lv>, xs: List<&2, Ef.Lv>) -> Maybe<&2, Ef.Lv>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      es.if(Maybe<&2, Ef.Lv>, es.has(lad, x), Some{x}, es.pick(lad, rest))

# the other levels in the clamp's order: up the ladder from l, then down
def es.others(l: Ef.Lv) -> List<&2, Ef.Lv>:
  match l:
    case Ef.Off{}:
      [Ef.Minimal{}, Ef.Low{}, Ef.Medium{}, Ef.High{}, Ef.Xhigh{}, Ef.Max{}]
    case Ef.Minimal{}:
      [Ef.Low{}, Ef.Medium{}, Ef.High{}, Ef.Xhigh{}, Ef.Max{}, Ef.Off{}]
    case Ef.Low{}:
      [Ef.Medium{}, Ef.High{}, Ef.Xhigh{}, Ef.Max{}, Ef.Minimal{}, Ef.Off{}]
    case Ef.Medium{}:
      [Ef.High{}, Ef.Xhigh{}, Ef.Max{}, Ef.Low{}, Ef.Minimal{}, Ef.Off{}]
    case Ef.High{}:
      [Ef.Xhigh{}, Ef.Max{}, Ef.Medium{}, Ef.Low{}, Ef.Minimal{}, Ef.Off{}]
    case Ef.Xhigh{}:
      [Ef.Max{}, Ef.High{}, Ef.Medium{}, Ef.Low{}, Ef.Minimal{}, Ef.Off{}]
    case Ef.Max{}:
      [Ef.Xhigh{}, Ef.High{}, Ef.Medium{}, Ef.Low{}, Ef.Minimal{}, Ef.Off{}]

# the first level of xs, else d
def es.first(xs: List<&2, Ef.Lv>, d: Ef.Lv) -> Ef.Lv:
  match xs:
    case Nil{}:
      d
    case x <> rest:
      x

# the last level of xs, else d
def es.last(xs: List<&2, Ef.Lv>, d: Ef.Lv) -> Ef.Lv:
  match xs:
    case Nil{}:
      d
    case x <> rest:
      es.last(rest, x)

def es.or(m: Maybe<&2, Ef.Lv>, d: Ef.Lv) -> Ef.Lv:
  match m:
    case Some{x}:
      x
    case None{}:
      d

# the clamp of l to the offered levels lad: l when offered; else the first
# offered level up the ladder from it, else down the ladder from it; off
# with no offered level (a nonempty lad without l always has a level up
# or down from l, so the last fallback, the head of lad, is reached only
# for an empty lad, where it is off)
def es.clamp(+lad: List<&2, Ef.Lv>, +l: Ef.Lv) -> Ef.Lv:
  es.if(Ef.Lv, es.has(lad, l), l, es.or(es.pick(lad, es.others(l)), es.first(lad, Ef.Off{})))

# xs has at least two levels
def es.two(xs: List<&2, Ef.Lv>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      match rest:
        case Nil{}:
          False{}
        case y <> more:
          True{}

# the level after the first c of xs, top past the end
def es.after(xs: List<&2, Ef.Lv>, +c: Ef.Lv, +top: Ef.Lv) -> Maybe<&2, Ef.Lv>:
  match xs:
    case Nil{}:
      None{}
    case x <> +rest:
      es.if(Maybe<&2, Ef.Lv>, es.same(x, c), Some{es.first(rest, top)}, es.after(rest, c, top))

# the level before the first c of xs, prev before the head
def es.before(xs: List<&2, Ef.Lv>, +c: Ef.Lv, prev: Ef.Lv) -> Maybe<&2, Ef.Lv>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      es.if(Maybe<&2, Ef.Lv>, es.same(x, c), Some{prev}, es.before(rest, c, x))

# one step from c along lad, wrapping at the ends
def es.step(d: Ef.Dir, +lad: List<&2, Ef.Lv>, +c: Ef.Lv) -> Maybe<&2, Ef.Lv>:
  match d:
    case Ef.Forward{}:
      es.after(lad, c, es.first(lad, Ef.Off{}))
    case Ef.Backward{}:
      es.before(lad, c, es.last(lad, Ef.Off{}))

# a cycle step: nothing with fewer than two offered levels; else one step
# from the clamp of l, wrapping at the ends
def es.cycle(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, d: Ef.Dir) -> Maybe<&2, Ef.Lv>:
  es.if(Maybe<&2, Ef.Lv>, es.two(lad), es.step(d, lad, es.clamp(lad, l)), None{})

# Speller
# -------

def es.lv(l: Ef.Lv, rest: String) -> String:
  Wr.put_nat(es.idx(l), rest)

def es.mlv(m: Maybe<&2, Ef.Lv>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{l}:
      Wr.put_nat(1n, es.lv(l, rest))

def es.reply(q: FEf.Req) -> String:
  match q:
    case FEf.Offered{f}:
      Wr.put_list(~Ef.Lv, ~es.lv, es.offered(f), "")
    case FEf.Clamp{f, l}:
      es.lv(es.clamp(es.offered(f), l), "")
    case FEf.Cycle{f, l, d}:
      es.mlv(es.cycle(es.offered(f), l, d), "")

def es.end(whole: Bool, q: FEf.Req) -> String:
  match whole:
    case True{}:
      es.reply(q)
    case False{}:
      Wr.err("ladder request: input left over")

def es.run(r: Wr.Dec<FEf.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      es.end(Wr.end(s), q)
    case Wr.Bad{}:
      Wr.err("ladder request: malformed")

# the reply to the input s
def es.spec(s: String) -> String:
  es.run(er.read(s))

# LAW core_effort_ffi_exact (R1-R3): on every input the entry answers, for the request the input starts with, the levels the model offers (in ladder order: by the chosen ladder or the reasoning default ladder for a reasoning model, by the plain default ladder for another), the clamp of the level (the level when offered, else the nearest offered level up the ladder, else down, off with none) or the cycle step (none with fewer than two offered levels, else the next or the previous offered level from the clamp, wrapping), spelled as the Rust reader reads it, when nothing follows the request; "ladder request: input left over" when something does; "ladder request: malformed" when the input starts with no request
# EXCLUDES: a clamp that goes down before up, or to a level not offered;
#   a cycle from the unclamped level or with no wrap; levels out of
#   ladder order; a reply in another spelling; a value for an input that
#   is no request (an unknown tag, a list cut short, a 15-digit number) or
#   for a request with input left over; another error text
law core_effort_ffi_exact:
  for +s: String
  {FEf.ffi(s) == es.spec(s) : String}

# (S10) The session, pinned
# -------------------------
# The session of bend/effort.bend (header §4) over the decisions above;
# a model offers what `es.offer` keeps with the default ladders of §1
def es.thinks() -> List<&2, Ef.Lv>:
  [Ef.Off{}, Ef.Minimal{}, Ef.Low{}, Ef.Medium{}, Ef.High{}]

# the levels the catalog model m offers
def es.lad(m: Ef.Mdl) -> List<&2, Ef.Lv>:
  match m:
    case Ef.Mdl{r, map}:
      es.offer(es.ladder(), r, map, es.thinks(), [Ef.Off{}])

# l fitted to the catalog model: clamped, unchanged without one
def es.fit(mo: Maybe<&2, Ef.Mdl>, +l: Ef.Lv) -> Ef.Lv:
  match mo:
    case None{}:
      l
    case Some{m}:
      es.clamp(es.lad(m), l)

# open: the model kept, the stored level (else the default) fitted
def es.open(s: Ef.Sess, dflt: Ef.Lv) -> Ef.Sess:
  match s:
    case Ef.Sess{+mo, st}:
      Ef.Sess{mo, Some{es.fit(mo, es.or(st, dflt))}}

# a switch to m: a stored level clamped to m; no stored level stays none
def es.switched(+m: Ef.Mdl, st: Maybe<&2, Ef.Lv>) -> Maybe<&2, Ef.Lv>:
  match st:
    case None{}:
      None{}
    case Some{l}:
      Some{es.clamp(es.lad(m), l)}

# the level a cycle step stores: the step's level, clamped as Rust's
# `apply_thinking_level` clamps it; l when the step gives none
def es.stepped.to(+lad: List<&2, Ef.Lv>, r: Maybe<&2, Ef.Lv>, l: Ef.Lv) -> Ef.Lv:
  match r:
    case None{}:
      l
    case Some{k}:
      es.clamp(lad, k)

# a cycle step of the stored level along the catalog model's levels; no
# step without a catalog model or a stored level
def es.stepped(st: Maybe<&2, Ef.Lv>, mo: Maybe<&2, Ef.Mdl>, d: Ef.Dir) -> Maybe<&2, Ef.Lv>:
  match st:
    case None{}:
      None{}
    case Some{+l}:
      match mo:
        case None{}:
          Some{l}
        case Some{+m}:
          Some{es.stepped.to(es.lad(m), es.cycle(es.lad(m), l, d), l)}

# one action: a switch sets the model and clamps the stored level to it; a
# set stores the requested level fitted; a cycle step stores the level it
# gives
def es.act(a: Ef.Act, s: Ef.Sess) -> Ef.Sess:
  match a:
    case Ef.Switch{+m}:
      match s:
        case Ef.Sess{mo, st}:
          Ef.Sess{Some{m}, es.switched(m, st)}
    case Ef.SetLevel{k}:
      match s:
        case Ef.Sess{+mo, st}:
          Ef.Sess{mo, Some{es.fit(mo, k)}}
    case Ef.Step{d}:
      match s:
        case Ef.Sess{+mo, st}:
          Ef.Sess{mo, es.stepped(st, mo, d)}

# the actions in order
def es.acts(acts: List<&2, Ef.Act>, s: Ef.Sess) -> Ef.Sess:
  match acts:
    case Nil{}:
      s
    case a <> rest:
      es.acts(rest, es.act(a, s))

# the level the runtime sends: the stored level, else off, fitted
def es.sent(s: Ef.Sess) -> Ef.Lv:
  match s:
    case Ef.Sess{mo, st}:
      es.fit(mo, es.or(st, Ef.Off{}))

# the display: `default` with no stored level, else the stored level fitted
def es.shown(s: Ef.Sess) -> Ef.Shown:
  match s:
    case Ef.Sess{mo, st}:
      match st:
        case None{}:
          Ef.Default{}
        case Some{l}:
          Ef.Level{es.fit(mo, l)}

# LAW effort_open_exact (S10): open keeps the model and stores the stored level, else the default, fitted to it, for every session and default
# EXCLUDES: an open that drops the stored level for the default (or the
#   default for off), skips the fit, or clamps to another model's levels
law effort_open_exact:
  for +s: Ef.Sess
  for +dflt: Ef.Lv
  {Ef.open(s, dflt) == es.open(s, dflt) : Ef.Sess}

# LAW effort_act_exact (S10): one action on any session: a switch sets the model and clamps the stored level to it, a set stores the requested level fitted, a cycle step stores the level the step gives (the level kept when it gives none)
# EXCLUDES: a switch that resets the level (to the clamp of off) or keeps
#   the old model; a set or a step that keeps the old level; a step from
#   the unclamped level or along another model's levels
law effort_act_exact:
  for +a: Ef.Act
  for +s: Ef.Sess
  {Ef.act(a, s) == es.act(a, s) : Ef.Sess}

# LAW effort_run_exact (S10): a run of actions is the actions one by one, in order, from any session
# EXCLUDES: a run that drops, repeats or reorders an action
law effort_run_exact:
  for +acts: List<&2, Ef.Act>
  for +s: Ef.Sess
  {Ef.run(acts, s) == es.acts(acts, s) : Ef.Sess}

# LAW effort_sent_exact (S10): the runtime sends the stored level, else off, fitted to the model, for any session
# EXCLUDES: a sent level unfitted, or the default instead of off
law effort_sent_exact:
  for +s: Ef.Sess
  {Ef.sent(s) == es.sent(s) : Ef.Lv}

# LAW effort_shown_exact (S10): the display shows `default` with no stored level, else the stored level fitted to the model, for any session
# EXCLUDES: a display of off for no stored level, or of the unfitted level
law effort_shown_exact:
  for +s: Ef.Sess
  {Ef.shown(s) == es.shown(s) : Ef.Shown}
